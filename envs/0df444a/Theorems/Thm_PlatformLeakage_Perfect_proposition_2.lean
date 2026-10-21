-- Prove2me | Theorems.Thm_PlatformLeakage_Perfect_proposition_2
-- name    : PlatformLeakage.Perfect.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:28.935451+00:00
-- url     : https://prove2.me/theorems/b984041d-08c9-4cb9-9b83-f803e53027da
-- title:
--   Proposition 2, p. 18 — the payout ratios ω^{j*} of (23) are optimal for (15), with optimal profit rate (24)
-- statement:
--   Under the standing assumptions, let
--   $$\omega^{j*}=\begin{cases}\dfrac{\widehat K^j}{g_2(N^j,v^j)},&\text{if }\widehat K^j\le\dfrac{c\phi\mu}{N^j}\Big(\sqrt{1+\tfrac{N^jv^j}{c\phi}}-1\Big)^2-\mu R_o\Big(1-\sqrt{\tfrac{c\phi}{c\phi+N^jv^j}}\Big),\\[2mm]0,&\text{otherwise,}\end{cases}\qquad j=h,l. \tag{23}$$
--   Then $(\omega^{h*},\omega^{l*})$ is an optimal solution of the platform's problem (15). If moreover $\widehat K^h>0$ and $\widehat K^l>0$, the optimal profit rate is
--   $$\Pi(\omega^{h*},\omega^{l*})=\sum_{j=h,l}\left(c\phi\mu\Big(\sqrt{1+\tfrac{N^jv^j}{c\phi}}-1\Big)^2-N^j\Big(\widehat K^j+\mu R_o\,\frac{\sqrt{1+N^jv^j/(c\phi)}-1}{\sqrt{1+N^jv^j/(c\phi)}}\Big)\right)^+. \tag{24}$$
--
--   The platform either pays exactly enough to keep all $j$-type providers or pays nothing and loses them, whichever is more profitable.
--
--   **Formalization Note** The value (24) is stated only when $\widehat K^j>0$ for both types: if $K^j=0$ and $R_o\ge v^j$ then $\widehat K^j=0$, all $j$-types stay on the platform at every payout ratio, and the $j$-term of the optimal profit is negative rather than the positive part in (24).
-- source:
--   He, Savin, Goh & Teo, Off-Platform Threats in On-Demand Services, SSRN working paper 3550646 (PDF of 2021-03-25), p. 18 (PDF 18), Proposition 2, (23)–(24); proof, Appendix p. 4 (PDF 39)

import Mathlib
import Definitions.Def_PlatformLeakage_Perfect_Model

namespace PlatformLeakage.Perfect

/-- Proposition 2 (p. 18): the payout ratios `ω^{j*}` of (23) solve the platform's problem (15); and,
when `K̂^h, K̂^l > 0`, the optimal profit rate is the value (24). -/
theorem proposition_2 (P : Params) (hP : P.Std) :
    IsOptimalPayout P (omegaStar P) ∧
    ((∀ j, 0 < Khat P j) →
      profit P (omegaStar P) =
        ∑ j ∈ ({PType.h, PType.l} : Finset PType),
          max (P.c * P.phi * P.mu *
                (Real.sqrt (1 + (P.N j : ℝ) * P.v j / (P.c * P.phi)) - 1) ^ 2 -
              (P.N j : ℝ) * (Khat P j + P.mu * P.Ro *
                ((Real.sqrt (1 + (P.N j : ℝ) * P.v j / (P.c * P.phi)) - 1) /
                  Real.sqrt (1 + (P.N j : ℝ) * P.v j / (P.c * P.phi))))) 0) := by sorry

end PlatformLeakage.Perfect
