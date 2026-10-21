-- Prove2me | Theorems.Thm_PlatformLeakage_Perfect_a9_ii
-- name    : PlatformLeakage.Perfect.a9_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:31.54286+00:00
-- url     : https://prove2.me/theorems/0f70e089-7f39-4ed5-a6e0-04efd3479304
-- title:
--   Proof of Proposition 3, Appendix p. 4, (A9)(ii) — with ω = g2(1, v^j − Ro)/g2(N^j, v^j), (1 − ω)g1(N^j, v^j) < Ro iff Ro > a^j
-- statement:
--   Under the standing assumptions, for each type $j$ with $R_o<v^j$, put $\omega=g_2(1,v^j-R_o)/g_2(N^j,v^j)$. Then
--   $$\big(1-\omega\big)\,g_1(N^j,v^j)<R_o\iff R_o>a^j,$$
--   where
--   $$a^j=v^j+c\phi\left(1-\left(\Big(1-\sqrt{\tfrac{N^j-1}{N^j}}\Big)\sqrt{1+\tfrac{N^jv^j}{c\phi}}+\sqrt{\tfrac{N^j-1}{N^j}}\right)^2\right).$$
--
--   When the off-platform option is the binding outside option, $\omega$ is the payout ratio of (23) and $g_1(N^j,v^j)=Q^j_p(N^j)$ is the on-platform fee (Lemma 2), so the left-hand side says the platform's margin $(1-\omega^{j*})Q^j_p(N^j)-R_o$ on $j$-type service is negative. This is condition (A9)(ii) of the proof of Proposition 3, and $a^j$ is the lower end-point of the leakage interval.
-- source:
--   He, Savin, Goh & Teo, Off-Platform Threats in On-Demand Services, SSRN working paper 3550646 (PDF of 2021-03-25), proof of Proposition 3, Appendix p. 4 (PDF 39), (A9)(ii) and its simplification

import Mathlib
import Definitions.Def_PlatformLeakage_Perfect_Model

namespace PlatformLeakage.Perfect

/-- Proof of Proposition 3, (A9)(ii) (Appendix p. 4): for `R_o < v^j`, with
`ω = g2(1, v^j − R_o)/g2(N^j, v^j)` and `Q^j_p(N^j) = g1(N^j, v^j)`, the platform's margin
`(1 − ω) Q^j_p(N^j) − R_o` is negative iff `R_o > a^j`. -/
theorem a9_ii (P : Params) (hP : P.Std) (j : PType) (hRo : P.Ro < P.v j) :
    (1 - g2 P 1 (P.v j - P.Ro) / g2 P (P.N j) (P.v j)) * g1 P (P.N j) (P.v j) < P.Ro ↔
      leakLo P j < P.Ro := by sorry

end PlatformLeakage.Perfect
