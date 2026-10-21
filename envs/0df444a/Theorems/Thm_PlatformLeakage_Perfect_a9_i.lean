-- Prove2me | Theorems.Thm_PlatformLeakage_Perfect_a9_i
-- name    : PlatformLeakage.Perfect.a9_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:40.761547+00:00
-- url     : https://prove2.me/theorems/22fce84a-3535-4697-8acc-80c22cbff965
-- title:
--   Proof of Proposition 3, Appendix p. 4, (A9)(i) — the off-platform utility g2(1, (v^j − Ro)^+) − K^j is positive iff Ro < b^j
-- statement:
--   Under the standing assumptions, for each type $j$,
--   $$g_2\big(1,(v^j-R_o)^+\big)-K^j>0\iff R_o<b^j=v^j+c\phi\Big(1-\Big(1+\sqrt{\tfrac{K^j}{c\phi\mu}}\Big)^2\Big).$$
--
--   By Lemma 2 the left-hand side is the off-platform utility rate $U^j_o$. This is condition (A9)(i) of the proof of Proposition 3: $j$-type providers can leak only while the off-platform option still beats the outside option, and $b^j$ is the upper end-point of the leakage interval.
--
--   **Formalization Note** The paper writes $g_2(1,v^j-R_o)$; the positive part keeps $g_2$ on its domain and is needed when $R_o\ge v^j$ (then both sides are false).
-- source:
--   He, Savin, Goh & Teo, Off-Platform Threats in On-Demand Services, SSRN working paper 3550646 (PDF of 2021-03-25), proof of Proposition 3, Appendix p. 4 (PDF 39), (A9)(i) and its simplification

import Mathlib
import Definitions.Def_PlatformLeakage_Perfect_Model

namespace PlatformLeakage.Perfect

/-- Proof of Proposition 3, (A9)(i) (Appendix p. 4): the off-platform utility rate
`g2(1, (v^j − R_o)⁺) − K^j` is positive iff `R_o < b^j`. -/
theorem a9_i (P : Params) (hP : P.Std) (j : PType) :
    0 < g2 P 1 (max (P.v j - P.Ro) 0) - P.K j ↔ P.Ro < leakHi P j := by sorry

end PlatformLeakage.Perfect
