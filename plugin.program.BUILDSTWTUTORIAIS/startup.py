# Python code by TWTUTORIAIS
 

import base64, codecs
magic = 'IyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIwojICAgICAgICAgICAgICAgICAgICAgICAgICAgICAvVCAvSSAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAjCiMgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAvIHwvIHwgLi1+LyAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICMKIyAgICAgICAgICAgICAgICAgICAgICAgICAgVFwgWSAgSSAgfC8gIC8gIF8gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIwojICAgICAgICAgL1QgICAgICAgICAgICAgICB8IFxJICB8ICBJICBZLi1+LyAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAjCiMgICAgICAgIEkgbCAgIC9JICAgICAgIFRcIHwgIHwgIGwgIHwgIFQgIC8gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICMKIyAgICAgVFwgfCAgXCBZIGwgIC9UICAgfCBcSSAgbCAgIFwgYCAgbCBZICAgICAgIElmIHlvdXIgZ29pbmcgdG8gY29weSAgICAgIwojIF9fICB8IFxsICAgXGwgIFxJIGwgX19sICBsICAgXCAgIGAgIF8uIHwgICAgICAgdGhpcyBhZGRvbiBqdXN0ICAgICAgICAgICAjCiMgXCB+LWwgIGBcICAgYFwgIFwgIFwgflwgIFwgICBgLiAuLX4gICB8ICAgICAgICBnaXZlIGNyZWRpdCEgICAgICAgICAgICAgICMKIyAgXCAgIH4tLiAiLS4gIGAgIFwgIF4uXyBeLiAiLS4gIC8gIFwgICB8ICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIwojLi0tfi0uXyAgfi0gIGAgIF8gIH4tXy4tIi0uIiAuXyAvLl8gLiIgLi8gICAgICAgIFN0b3AgRGVsZXRpbmcgdGhlICAgICAgICAjCiMgPi0tLiAgfi0uICAgLl8gIH4+LSIgICAgIlwgICA3ICAgNyAgIF0gICAgICAgICAgY3JlZGl0cyBmaWxlISAgICAgICAgICAgICMKI14uX19ffiItLS5fICAgIH4teyAgLi1+IC4gIGBcIFkgLiAvICAgIHwgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIwojIDxfXyB+Ii0uICB+ICAgICAgIC9fLyAgIFwgICBcSSAgWSAgIDogfCAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAjCiMgICBeLS5fXyAgICAgICAgICAgfihfLyAgIFwgICA+Ll86ICAgfCBsX19fX19fICAgICAgICAgICAgICAgICAgICAgICAgICAgICMKIyAgICAgICBeLS0uLF9fXy4tfiIgIC9fLyAgICEgIGAtLn4iLS1sXyAvICAgICB+Ii0uICAgICAgICAgICAgICAgICAgICAgICAgIwojICAgICAgICAgICAgICAoXy8gLiAgfiggICAvJyAgICAgIn4iLS0sWSAgIC09Yi0uIF8pICAgICAgICAgICAgICAgICAgICAgICAjCiMgICAgICAgICAgICAgICAoXy8gLiAgXCAgOiAgICAgICAgICAgLyBsICAgICAgYyJ+byBcICAgICAgICAgICAgICAgICAgICAgICMKIyAgICAgICAgICAgICAgICBcIC8gICAgYC4gICAgLiAgICAgLl4gICBcXy4tfiJ+LS0uICApICAgICAgICAgICAgICAgICAgICAgIwojICAgICAgICAgICAgICAgICAoXy8gLiAgIGAgIC8gICAgIC8gICAgICAgISAgICAgICApLyAgICAgICAgICAgICAgICAgICAgICAjCiMgICAgICAgICAgICAgICAgICAvIC8gXy4gICAnLiAgIC4nOiAgICAgIC8gICAgICAgICcgICAgICAgICAgICAgICAgICAgICAgICMKIyAgICAgICAgICAgICAgICAgIH4oXy8gLiAgIC8gICAgXyAgYCAgLi08XyAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIwojICAgICAgICAgICAgICAgICAgICAvXy8gLiAnIC4tfiIgYC4gIC8gXCAgXCAgICAgICAgICAsej0uICBTdXJmYWNpbmd4ICAgICAjCiMgICAgICAgICAgICAgICAgICAgIH4oIC8gICAnICA6ICAgfCBLICAgIi0ufi0uX19fX19fLy8gICBPcmlnaW5hbCBBdXRob3IgICMKIyAgICAgICAgICAgICAgICAgICAgICAiLSwuICAgIGwgICBJLyBcXyAgICBfX3stLS0+Ll8oPT0uICAgICAgICAgICAgICAgICAgIwojICAgICAgICAgICAgICAgICAgICAgICAvLyggICAgIFwgIDwgICAgfiJ+IiAgICAgLy8gICAgICAgICAgICAgICAgICAgICAgICAjCiMgICAgICAgICAgICAgICAgICAgICAgLycgL1wgICAgIFwgIFwgICAgICx2PS4gICgoICAgICBGaXJlIFRWIEd1cnUgICAgICAgICMKIyAgICAgICAgICAgICAgICAgICAgLl4uIC8gL1wgICAgICIgIH1fXyAvLz09PS0gIGAgICAgUHlYQk1DdCBMYVlPVXQgICAgICAgIwojICAgICAgICAgICAgICAgICAgIC8gLyAnICcgICItLixfXyB7LS0tKD09LSAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAjCiMgICAgICAgICAgICAgICAgIC5eICcgICAgICAgOiAgVCAgfiIgICBsbCAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICMKIyAgICAgICAgICAgICAgICAvIC4gIC4gIC4gOiB8IDohICAgICAgICBcICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIwojICAgICAgICAgICAgICAgKF8vICAvICAgfCB8IGotIiAgICAgICAgICB+XiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAjCiMgICAgICAgICAgICAgICAgIH4tPF8oXy5eLX4iICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICMKIyAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIwojICAgICAgICAgICAgICAgICAgQ29weXJpZ2h0IChDKSBPbmUgb2YgdGhvc2UgWWVhcnMuLi4uICAgICAgICAgICAgICAgICAgICAjCiMgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICMKIyAgVGhpcyBwcm9ncmFtIGlzIGZyZWUgc29mdHdhcmU6IHlvdSBjYW4gcmVkaXN0cmlidXRlIGl0IGFuZC9vciBtb2RpZnkgICAgIwojICBpdCB1bmRlciB0aGUgdGVybXMgb2YgdGhlIEdOVSBHZW5lcmFsIFB1YmxpYyBMaWNlbnNlIGFzIHB1Ymxpc2hlZCBieSAgICAjCiMgIHRoZSBGcmVlIFNvZnR3YXJlIEZvdW5kYXRpb24sIGVpdGhlciB2ZXJzaW9uIDMgb2YgdGhlIExpY2Vuc2UsIG9yICAgICAgICMKIyAgKGF0IHlvdXIgb3B0aW9uKSBhbnkgbGF0ZXIgdmVyc2lvbi4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIwojICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAjCiMgIFRoaXMgcHJvZ3JhbSBpcyBkaXN0cmlidXRlZCBpbiB0aGUgaG9wZSB0aGF0IGl0IHdpbGwgYmUgdXNlZnVsLCAgICAgICAgICMKIyAgYnV0IFdJVEhPVVQgQU5ZIFdBUlJBTlRZOyB3aXRob3V0IGV2ZW4gdGhlIGltcGxpZWQgd2FycmFudHkgb2YgICAgICAgICAgIwojICBNRVJDSEFOVEFCSUxJVFkgb3IgRklUTkVTUyBGT1IgQSBQQVJUSUNVTEFSIFBVUlBPU0UuICBTZWUgdGhlICAgICAgICAgICAjCiMgIEdOVSBHZW5lcmFsIFB1YmxpYyBMaWNlbnNlIGZvciBtb3JlIGRldGFpbHMuICAgICAgICAgICAgICAgICAgICAgICAgICAgICMKIyAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIwojIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjIyMjCgppbXBvcnQgeGJtYywgeGJtY2FkZG9uLCB4Ym1jZ3VpLCB4Ym1jcGx1Z2luLCBvcywgc3lzLCB4Ym1jdmZzLCBnbG9iCmltcG9ydCBzaHV0aWwKaW1wb3J0IHVybGxpYi5yZXF1ZXN0LCB1cmxsaWIuZXJyb3IsIHVybGxpYi5wYXJzZQppbXBvcnQgcmUKaW1wb3J0IHVzZXJ2YXIKZnJvbSBkYXRldGltZSBpbXBvcnQgZGF0ZSwgZGF0ZXRpbWUsIHRpbWVkZWx0YQpmcm9tIHJlc291cmNlcy5saWJzIGltcG9ydCBleHRyYWN0LCBkb3dubG9hZGVyLCBub3RpZnksIGxvZ2luaXQsIGRlYnJpZGl0LCBhbGx1Y2l0LCB0cmFrdGl0LCBza2luU3dpdGNoLCB1cGxvYWRMb2csIHdpemFyZCBhcyB3aXoKCkFERE9OX0lEICAgICAgID0gdXNlcnZhci5BRERPTl9JRApBRERPTlRJVExFICAgICA9IHVzZXJ2YXIuQURET05USVRMRQpBRERPTiAgICAgICAgICA9IHdpei5hZGRvbklkKEFERE9OX0lEKQpWRVJTSU9OICAgICAgICA9IHdpei5hZGRvbkluZm8oQURET05fSUQsJ3ZlcnNpb24nKQpBRERPTlBBVEggICAgICA9IHdpei5hZGRvbkluZm8oQURET05fSUQsJ3BhdGgnKQpBRERPTklEICAgICAgICA9IHdpei5hZGRvbkluZm8oQURET05fSUQsJ2lkJykKRElBTE9HICAgICAgICAgPSB4Ym1jZ3VpLkRpYWxvZygpCkRQICAgICAgICAgICAgID0geGJtY2d1aS5EaWFsb2dQcm9ncmVzcygpCkhPTUUgICAgICAgICAgID0geGJtY3Zmcy50cmFuc2xhdGVQYXRoKCdzcGVjaWFsOi8vaG9tZS8nKQpQUk9GSUxFICAgICAgICA9IHhibWN2ZnMudHJhbnNsYXRlUGF0aCgnc3BlY2lhbDovL3Byb2ZpbGUvJykKS09ESUhPTUUgICAgICAgPSB4Ym1jdmZzLnRyYW5zbGF0ZVBhdGgoJ3NwZWNpYWw6Ly94Ym1jLycpCkFERE9OUyAgICAgICAgID0gb3MucGF0aC5qb2luKEhPTUUsICAgICAnYWRkb25zJykKS09ESUFERE9OUyAgICAgPSBvcy5wYXRoLmpvaW4oS09ESUhPTUUsICdhZGRvbnMnKQpVU0VSREFUQSAgICAgICA9IG9zLnBhdGguam9pbihIT01FLCAgICAgJ3VzZXJkYXRhJykKUExVR0lOICAgICAgICAgPSBvcy5wYXRoLmpvaW4oQURET05TLCAgIEFERE9OX0lEKQpQQUNLQUdFUyAgICAgICA9IG9zLnBhdGguam9pbihBRERPTlMsICAgJ3BhY2thZ2VzJykKQURET05EQVRBICAgICAgPSBvcy5wYXRoLmpvaW4oVVNFUkRBVEEsICdhZGRvbl9kYXRhJywgQURET05fSUQpClRFWFRDQUNIRSAgICAgID0gb3MucGF0aC5qb2luKEFERE9OREFUQSwgJ0NhY2hlJykKRkFOQVJUICAgICAgICAgPSBvcy5wYXRoLmpvaW4oQURET05QQVRILCdmYW5hcnQuanBnJykKSUNPTiAgICAgICAgICAgPSBvcy5wYXRoLmpvaW4oQURET05QQVRILCdpY29uLnBuZycpCkFSVCAgICAgICAgICAgID0gb3MucGF0aC5qb2luKEFERE9OUEFUSCwncmVzb3VyY2VzJywgJ2FydCcpClNLSU4gICAgICAgICAgID0geGJtYy5nZXRTa2luRGlyKCkKVEhVTUJTICAgICAgICAgPSBvcy5wYXRoLmpvaW4oVVNFUkRBVEEsICAnVGh1bWJuYWlscycpCkJVSUxETkFNRSAgICAgID0gd2l6LmdldFMoJ2J1aWxkbmFtZScpCkRFRkFVTFRTS0lOICAgID0gd2l6LmdldFMoJ2RlZmF1bHRza2luJykKREVGQVVMVE5BTUUgICAgPSB3aXouZ2V0UygnZGVmYXVsdHNraW5uYW1lJykKREVGQVVMVElHTk9SRSAgPSB3aXouZ2V0UygnZGVmYXVsdHNraW5pZ25vcmUnKQpCVUlMRFZFUlNJT04gICA9IHdpei5nZXRTKCdidWlsZHZlcnNpb24nKQpCVUlMRExBVEVTVCAgICA9IHdpei5nZXRTKCdsYXRlc3R2ZXJzaW9uJykKQlVJTERDSEVDSyAgICAgPSB3aXouZ2V0UygnbGFzdGJ1aWxkY2hlY2snKQpESVNBQkxFVVBEQVRFICA9IHdpei5nZXRTKCdkaXNhYmxldXBkYXRlJykKQVVUT0NMRUFOVVAgICAgPSB3aXouZ2V0UygnYXV0b2NsZWFuJykKQVVUT0NBQ0hFICAgICAgPSB3aXouZ2V0UygnY2xlYXJjYWNoZScpCkFVVE9QQUNLQUdFUyAgID0gd2l6LmdldFMoJ2NsZWFycGFja2FnZXMnKQpBVVRPVEhVTUJTICAgICA9IHdpei5nZXRTKCdjbGVhcnRodW1icycpCkFVVE9GRVEgICAgICAgID0gd2l6LmdldFMoJ2F1dG9jbGVhbmZlcScpCkFVVE9ORVhUUlVOICAgID0gd2l6LmdldFMoJ25leHRhdXRvY2xlYW51cCcpClRSQUtUU0FWRSAgICAgID0gd2l6LmdldFMoJ3RyYWt0bGFzdHNhdmUnKQpSRUFMU0FWRSAg'
love = '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'
god = 'dHkoIldpbmRvdy5pc1Zpc2libGUoeWVzbm9kaWFsb2cpIik6CgkJCXdpei5lYmkoJ1NlbmRDbGljaygxMSknKQoJCQl3aXoubG9va2FuZEZlZWxEYXRhKCdyZXN0b3JlJykKCQllbHNlOiB3aXouTG9nTm90aWZ5KCJbQ09MT1IgJXNdJXNbL0NPTE9SXSIgJSAoQ09MT1IxLCBBRERPTlRJVExFKSwnW0NPTE9SICVzXVNraW4gU3dhcCBUaW1lZCBPdXQhWy9DT0xPUl0nICUgQ09MT1IyKQoJd2l6LmxvZygiW0J1aWxkIENoZWNrXSBJbnZhbGlkIFNraW4gQ2hlY2sgRW5kIiwgeGJtYy5MT0dJTkZPKQoKd2hpbGUgeGJtYy5QbGF5ZXIoKS5pc1BsYXlpbmdWaWRlbygpOgoJeGJtYy5zbGVlcCgxMDAwKQoKaWYgS09ESVYgPj0gMTc6CglOT1cgPSBkYXRldGltZS5ub3coKQoJdGVtcCA9IHdpei5nZXRTKCdrb2RpMTdpc2NyYXAnKQoJaWYgbm90IHRlbXAgPT0gJyc6CgkJaWYgdGVtcCA+IHN0cihOT1cgLSB0aW1lZGVsdGEobWludXRlcz0yKSk6CgkJCXdpei5sb2coIktpbGxpbmcgU3RhcnQgVXAgU2NyaXB0IikKCQkJc3lzLmV4aXQoKQoJd2l6LmxvZygiJXMiICUgKE5PVykpCgl3aXouc2V0Uygna29kaTE3aXNjcmFwJywgc3RyKE5PVykpCgl4Ym1jLnNsZWVwKDEwMDApCglpZiBub3Qgd2l6LmdldFMoJ2tvZGkxN2lzY3JhcCcpID09IHN0cihOT1cpOgoJCXdpei5sb2coIktpbGxpbmcgU3RhcnQgVXAgU2NyaXB0IikKCQlzeXMuZXhpdCgpCgllbHNlOgoJCXdpei5sb2coIkNvbnRpbnVpbmcgU3RhcnQgVXAgU2NyaXB0IikKCmlmIEtPRElBRERPTlMgaW4gQURET05QQVRIOgoJd2l6LmxvZygiQ29weWluZyBwYXRoIHRvIGFkZG9ucyBkaXIiLCB4Ym1jLkxPR0lORk8pCglpZiBub3Qgb3MucGF0aC5leGlzdHMoQURET05TKTogb3MubWFrZWRpcnMoQURET05TKQoJbmV3cGF0aCA9IHhibWN2ZnMudHJhbnNsYXRlUGF0aChvcy5wYXRoLmpvaW4oJ3NwZWNpYWw6Ly9ob21lL2FkZG9ucy8nLCBBRERPTklEKSkKCWlmIG9zLnBhdGguZXhpc3RzKG5ld3BhdGgpOgoJCXdpei5sb2coIkZvbGRlciBhbHJlYWR5IGV4aXN0cywgY2xlYW5pbmcgSG91c2UiLCB4Ym1jLkxPR0lORk8pCgkJd2l6LmNsZWFuSG91c2UobmV3cGF0aCkKCQl3aXoucmVtb3ZlRm9sZGVyKG5ld3BhdGgpCgl0cnk6CgkJd2l6LmNvcHl0cmVlKEFERE9OUEFUSCwgbmV3cGF0aCkKCWV4Y2VwdCBFeGNlcHRpb24gYXMgZToKCQlwYXNzCgl3aXouZm9yY2VVcGRhdGUoVHJ1ZSkKCnRyeToKCW15YnVpbGRzID0geGJtY3Zmcy50cmFuc2xhdGVQYXRoKE1ZQlVJTERTKQoJaWYgbm90IG9zLnBhdGguZXhpc3RzKG15YnVpbGRzKTogeGJtY3Zmcy5ta2RpcnMobXlidWlsZHMpCmV4Y2VwdDoKCXBhc3MKCndpei5sb2coIltBdXRvIEluc3RhbGwgUmVwb10gU3RhcnRlZCIsIHhibWMuTE9HSU5GTykKaWYgQVVUT0lOU1RBTEwgPT0gJ1llcycgYW5kIG5vdCBvcy5wYXRoLmV4aXN0cyhvcy5wYXRoLmpvaW4oQURET05TLCBSRVBPSUQpKToKCXdvcmtpbmd4bWwgPSB3aXoud29ya2luZ1VSTChSRVBPQURET05YTUwpCglpZiB3b3JraW5neG1sID09IFRydWU6CgkJdmVyID0gd2l6LnBhcnNlRE9NKHdpei5vcGVuVVJMKFJFUE9BRERPTlhNTCksICdhZGRvbicsIHJldD0ndmVyc2lvbicsIGF0dHJzID0geydpZCc6IFJFUE9JRH0pCgkJaWYgbGVuKHZlcikgPiAwOgoJCQlpbnN0YWxsemlwID0gJyVzLSVzLnppcCcgJSAoUkVQT0lELCB2ZXJbMF0pCgkJCXdvcmtpbmdyZXBvID0gd2l6LndvcmtpbmdVUkwoUkVQT1pJUFVSTCtpbnN0YWxsemlwKQoJCQlpZiB3b3JraW5ncmVwbyA9PSBUcnVlOgoJCQkJRFAuY3JlYXRlKEFERE9OVElUTEUsJ0Rvd25sb2FkaW5nIFJlcG8uLi5cblBsZWFzZSBXYWl0JykKCQkJCWlmIG5vdCBvcy5wYXRoLmV4aXN0cyhQQUNLQUdFUyk6IG9zLm1ha2VkaXJzKFBBQ0tBR0VTKQoJCQkJbGliPW9zLnBhdGguam9pbihQQUNLQUdFUywgaW5zdGFsbHppcCkKCQkJCXRyeTogb3MucmVtb3ZlKGxpYikKCQkJCWV4Y2VwdDogcGFzcwoJCQkJZG93bmxvYWRlci5kb3dubG9hZChSRVBPWklQVVJMK2luc3RhbGx6aXAsbGliLCBEUCkKCQkJCWV4dHJhY3QuYWxsKGxpYiwgQURET05TLCBEUCkKCQkJCXRyeToKCQkJCQlmID0gb3Blbihvcy5wYXRoLmpvaW4oQURET05TLCBSRVBPSUQsICdhZGRvbi54bWwnKSwgbW9kZT0ncicsIGVuY29kaW5nPSd1dGYtOCcpOyBnID0gZi5yZWFkKCk7IGYuY2xvc2UoKQoJCQkJCW5hbWUgPSB3aXoucGFyc2VET00oZywgJ2FkZG9uJywgcmV0PSduYW1lJywgYXR0cnMgPSB7J2lkJzogUkVQT0lEfSkKCQkJCQl3aXouTG9nTm90aWZ5KCJbQ09MT1IgJXNdJXNbL0NPTE9SXSIgJSAoQ09MT1IxLCBuYW1lWzBdKSwgIltDT0xPUiAlc11BZGQtb24gdXBkYXRlZFsvQ09MT1JdIiAlIENPTE9SMiwgaWNvbj1vcy5wYXRoLmpvaW4oQURET05TLCBSRVBPSUQsICdpY29uLnBuZycpKQoJCQkJZXhjZXB0OgoJCQkJCXBhc3MKCQkJCWlmIEtPRElWID49IDE3OiB3aXouYWRkb25EYXRhYmFzZShSRVBPSUQsIDEpCgkJCQlEUC5jbG9zZSgpCgkJCQl4Ym1jLnNsZWVwKDUwMCkKCQkJCXdpei5mb3JjZVVwZGF0ZShUcnVlKQoJCQkJd2l6LmxvZygiW0F1dG8gSW5zdGFsbCBSZXBvXSBTdWNjZXNzZnVsbHkgSW5zdGFsbGVkIiwgeGJtYy5MT0dJTkZPKQoJCQllbHNlOiAKCQkJCXdpei5Mb2dOb3RpZnkoIltDT0xPUiAlc11SZXBvIEluc3RhbGwgRXJyb3JbL0NPTE9SXSIgJSBDT0xPUjEsICJbQ09MT1IgJXNdSW52YWxpZCB1cmwgZm9yIHppcCFbL0NPTE9SXSIgJSBDT0xPUjIpCgkJCQl3aXoubG9nKCJbQXV0byBJbnN0YWxsIFJlcG9dIFdhcyB1bmFibGUgdG8gY3JlYXRlIGEgd29ya2luZyB1cmwgZm9yIHJlcG9zaXRvcnkuICVzIiAlIHdvcmtpbmdyZXBvLCB4Ym1jLkxPR0VSUk9SKQoJCWVsc2U6CgkJCXdpei5sb2coIkludmFsaWQgVVJMIGZvciBSZXBvIFppcCIsIHhibWMuTE9HRVJST1IpCgllbHNlOiAKCQl3aXouTG9nTm90aWZ5KCJbQ09MT1IgJXNdUmVwbyBJbnN0YWxsIEVycm9yWy9DT0xPUl0iICUgQ09MT1IxLCAiW0NPTE9SICVzXUludmFsaWQgYWRkb24ueG1sIGZpbGUhWy9DT0xPUl0iICUgQ09MT1IyKQoJCXdpei5sb2coIltBdXRvIEluc3RhbGwgUmVwb10gVW5hYmxlIHRvIHJlYWQgdGhlIGFkZG9uLnhtbCBmaWxlLiIsIHhibWMuTE9HRVJST1IpCmVsaWYgbm90IEFVVE9JTlNUQUxMID09ICdZZXMnOiB3aXoubG9nKCJbQXV0byBJbnN0YWxsIFJlcG9dIE5vdCBFbmFibGVkIiwgeGJtYy5MT0dJTkZPKQplbGlmIG9zLnBhdGguZXhpc3RzKG9zLnBhdGguam9pbihBRERPTlMsIFJFUE9JRCkpOiB3aXoubG9nKCJbQXV0byBJbnN0YWxsIFJlcG9dIFJlcG9zaXRvcnkgYWxyZWFkeSBpbnN0YWxsZWQiKQoKd2l6LmxvZygiW0F1dG8gVXBkYXRlIFdpemFyZF0gU3RhcnRlZCIsIHhibWMuTE9HSU5GTykKaWYgQVVUT1VQREFURSA9PSAnWWVzJzoKCXdpei53aXphcmRVcGRhdGUoJ3N0YXJ0dXAnKQplbHNlOiB3aXoubG9nKCJbQXV0byBVcGRhdGUgV2l6YXJkXSBOb3QgRW5hYmxlZCIsIHhibWMuTE9HSU5GTykKCndpei5sb2coIltOb3RpZmljYXRpb25zXSBTdGFydGVkIiwgeGJtYy5MT0dJTkZPKQppZiBFTkFCTEUgPT0gJ1llcyc6CglpZiBub3QgTk9USUZZID09ICd0cnVlJzoKCQl1cmwgPSB3aXoud29ya2luZ1VSTChOT1RJRklDQVRJT04pCgkJaWYgdXJsID09IFRydWU6CgkJCWlkLCBtc2cgPSB3aXouc3BsaXROb3RpZnkoTk9USUZJQ0FUSU9OKQoJCQlpZiBub3QgaWQgPT0gRmFsc2U6CgkJCQl0cnk6CgkJCQkJaWQgPSBpbnQoaWQpOyBOT1RFSUQgPSBpbnQoTk9URUlEKQoJCQkJCWlmIGlkID09IE5PVEVJRDoKCQkJCQkJaWYgTk9URURJU01JU1MgPT0gJ2ZhbHNlJzoKCQkJCQkJCW5vdGlmeS5ub3RpZmljYXRpb24obXNnKQoJCQkJCQllbHNlOiB3aXoubG9nKCJbTm90aWZpY2F0aW9uc10gaWRbJXNdIERpc21pc3NlZCIgJSBpbnQoaWQpLCB4Ym1jLkxPR0lORk8pCgkJCQkJZWxpZiBpZCA+IE5PVEVJRDoKCQkJCQkJd2l6LmxvZygiW05vdGlmaWNhdGlvbnNdIGlkOiAlcyIgJSBzdHIoaWQpLCB4Ym1jLkxPR0lORk8pCgkJCQkJCXdpei5zZXRTKCdub3RlaWQnLCBzdHIoaWQpKQoJCQkJCQl3aXouc2V0Uygnbm90ZWRpc21pc3MnLCAnZmFsc2UnKQoJCQkJCQlub3RpZnkubm90aWZpY2F0aW9uKG1zZz1tc2cpCgkJCQkJCXdpei5sb2coIltOb3RpZmljYXRpb25zXSBDb21wbGV0ZSIsIHhibWMuTE9HSU5GTykKCQkJCWV4Y2VwdCBFeGNlcHRpb24gYXMgZToKCQkJCQl3aXoubG9nKCJFcnJvciBvbiBOb3RpZmljYXRpb25zIFdpbmRvdzogJXMiICUgc3RyKGUpLCB4Ym1jLkxPR0VSUk9SKQoJCQllbHNlOiB3aXoubG9nKCJbTm90aWZpY2F0aW9uc10gVGV4dCBGaWxlIG5vdCBmb3JtYXRlZCBDb3JyZWN0bHkiKQoJCWVsc2U6IHdpei5sb2coIltOb3RpZmljYXRpb25zXSBVUkwoJXMpOiAlcyIgJSAoTk9USUZJQ0FUSU9OLCB1cmwpLCB4Ym1jLkxPR0lORk8pCgllbHNlOiB3aXoubG9nKCJbTm90aWZpY2F0aW9uc10gVHVybmVkIE9mZiIsIHhibWMuTE9HSU5GTykKZWxzZTogd2l6LmxvZygiW05vdGlmaWNhdGlvbnNdIE5vdCBFbmFibGVkIiwgeGJtYy5MT0dJTkZPKQoKd2l6LmxvZygiW0luc3RhbGxlZCBDaGVja10gU3RhcnRlZCIsIHhibWMuTE9HSU5GTykKaWYgSU5TVEFMTEVEID09ICd0cnVlJzoKCWlmIEtPRElWID49IDE3OgoJCXdpei5rb2RpMTdGaXgoKQoJCWlmIFNLSU4gaW4gWydza2luLmNvbmZsdWVuY2UnLCAnc2tpbi5lc3R1YXJ5J106CgkJCWNoZWNrU2tpbigpCgkJRkFJTEVEID0gVHJ1ZQoJZWxpZiBub3QgRVhUUkFDVCA9PSAnMTAwJyBhbmQgbm90IEJVSUxETkFNRSA9PSAiIjoKCQl3aXoubG9nKCJbSW5zdGFsbGVkIENoZWNrXSBCdWlsZCB3YXMgZXh0cmFjdGVkICVzLzEwMCB3aXRoIFtFUlJPUlM6ICVzXSIgJSAoRVhUUkFDVCwgRVhURVJST1IpLCB4Ym1jLkxPR0lORk8pCgkJeWVzPURJQUxPRy55ZXNubyhBRERPTlRJVExFLCAnW0NPTE9SICVzXSVzWy9DT0xPUl0gW0NPTE9SICVzXXdhcyBub3QgaW5zdGFsbGVkIGNvcnJlY3RseSEnICUgKENPTE9SMSwgQ09MT1IyLCBCVUlMRE5BTUUpICsgJ1xuSW5zdGFsbGVkOiBbQ09MT1IgJXNdJXNbL0NPTE9SXSAvIEVycm9yIENvdW50OiBbQ09MT1IgJXNdJXNbL0NPTE9SXScgJSAoQ09MT1IxLCBFWFRSQUNULCBDT0xPUjEsIEVYVEVSUk9SKSArICdcbldvdWxkIHlvdSBsaWtlIHRvIHRyeSBhZ2Fpbj9bL0NPTE9SXScsIG5vbGFiZWw9J1tCXU5vIFRoYW5rcyFbL0JdJywgeWVzbGFiZWw9J1tCXVJldHJ5IEluc3RhbGxbL0JdJykKCQl3aXouY2xlYXJTKCdidWlsZCcpCgkJRkFJTEVEID0gVHJ1ZQoJCWlmIHllczogCgkJCXdpei5lYmkoIlBsYXlNZWRpYShwbHVnaW46Ly8lcy8/bW9kZT1pbnN0YWxsJm5hbWU9JXMmdXJsPWZyZXNoKSIgJSAoQURET05fSUQsIHVybGxpYi5wYXJzZS5xdW90ZV9wbHVzKEJVSUxETkFNRSkpKQoJCQl3aXoubG9nKCJbSW5zdGFsbGVkIENoZWNrXSBGcmVzaCBJbnN0YWxsIFJlLWFjdGl2YXRlZCIsIHhibWMuTE9HSU5GTykKCQllbHNlOiB3aXoubG9nKCJbSW5zdGFsbGVkIENoZWNrXSBSZWluc3RhbGwgSWdub3JlZCIpCgllbGlmIFNLSU4gaW4gWydza2luLmNvbmZsdWVuY2UnLCAnc2tpbi5lc3R1YXJ5J106CgkJd2l6LmxvZygiW0luc3RhbGxlZCBDaGVja10gSW5jb3JyZWN0IHNraW46ICVzIiAlIFNLSU4sIHhibWMuTE9HSU5GTykKCQlkZWZhdWx0cyA9IHdpei5nZXRTKCdkZWZhdWx0c2tpbicpCgkJaWYgbm90IGRlZmF1bHRzID09ICcn'
destiny = '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'
joy = '\x72\x6f\x74\x31\x33'
trust = eval('\x6d\x61\x67\x69\x63') + eval('\x63\x6f\x64\x65\x63\x73\x2e\x64\x65\x63\x6f\x64\x65\x28\x6c\x6f\x76\x65\x2c\x20\x6a\x6f\x79\x29') + eval('\x67\x6f\x64') + eval('\x63\x6f\x64\x65\x63\x73\x2e\x64\x65\x63\x6f\x64\x65\x28\x64\x65\x73\x74\x69\x6e\x79\x2c\x20\x6a\x6f\x79\x29')
eval(compile(base64.b64decode(eval('\x74\x72\x75\x73\x74')),'<string>','exec'))