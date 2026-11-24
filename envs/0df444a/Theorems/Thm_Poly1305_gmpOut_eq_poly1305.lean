-- Prove2me | Theorems.Thm_Poly1305_gmpOut_eq_poly1305
-- name    : Poly1305.gmpOut_eq_poly1305
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-24T07:39:40.030582+00:00
-- url     : https://prove2.me/theorems/74393e02-a3b2-4ef3-be86-2213814af9c3
-- title:
--   §2 — the sample code computes Poly1305_r(m, s)
-- statement:
--   For all 16-byte strings $r$ and $s$ and every message $m$, the output of the sample code `poly1305_gmpxx` (`gmpOut r s m`: the loop over chunks of $\min(16, l)$ bytes with $h \leftarrow ((h + c)\bar r) \bmod p$, then $h \leftarrow h + s$, then the bytes $\lfloor h/2^{8j} \rfloor \bmod 256$ for $j = 0, \dots, 15$) equals $\mathrm{Poly1305}_{\bar r}(m, s)$ as defined on p. 5, where $\bar r = r[0] + 2^8 r[1] + \dots + 2^{120} r[15]$. No condition on $r$ is assumed, as in the code.
-- source:
--   Bernstein, D. J., The Poly1305-AES message-authentication code, in: Fast Software Encryption (FSE 2005), Lecture Notes in Computer Science 3557, Springer, 2005, 32–49, https://doi.org/10.1007/11502760_3 (author's version of 2005-03-29: https://cr.yp.to/mac/poly1305-20050329.pdf), pp. 5–6, §2, Sample code

import Definitions.Def_Poly1305Bernstein

namespace Poly1305

theorem gmpOut_eq_poly1305 (r s : Str16) (m : Message) :
    gmpOut r s m = poly1305 (leVal r) m s := by
  sorry

end Poly1305
