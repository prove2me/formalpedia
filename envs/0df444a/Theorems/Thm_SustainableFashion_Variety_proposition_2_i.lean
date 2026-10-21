-- Prove2me | Theorems.Thm_SustainableFashion_Variety_proposition_2_i
-- name    : SustainableFashion.Variety.proposition_2_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:50.653821+00:00
-- url     : https://prove2.me/theorems/758e2273-cbe7-47af-92c4-f1c38cba2d17
-- title:
--   Proposition 2(i), p. 14 — for m > k′/k: û = θ/k′, q̂ = 0, EΠ = (n̄/2)(a + θ²/(2k′) + γ/2 − γ/(4m)) − βm
-- statement:
--   Fix parameters with $0<k<k'$, $\theta>0$ and $\bar n>0$, and a number of styles $m>k'/k$. Then the pair
--   $$\hat u=\frac{\theta}{k'},\qquad \hat q=0$$
--   maximises the expected profit (1) over quality $u\ge0$ and inventory $0\le q\le\bar n$, it is the only maximiser, and the maximal expected profit is
--   $$\mathbb E\Pi=\frac{\bar n}{2}\Big(a+\frac{\theta^2}{2k'}+\frac\gamma2-\frac\gamma{4m}\Big)-\beta m .$$
--
--   With many styles the firm relies on quick response alone, and its quality no longer depends on $m$.
--
--   **Formalization Note** No sign condition on $\beta$, $\gamma$ or $a$ is assumed: for a given $m$ they enter (1) only additively, as on the page. The hypothesis $\theta>0$ (consumers value quality) is what makes the maximiser unique; at $\theta=0$ the optimal quality is $0$ and every inventory is optimal.
-- source:
--   Long & Nasiry, Sustainability in the Fast Fashion Industry, SSRN 3486502 author's manuscript (2021; MSOM doi:10.1287/msom.2021.1054), Proposition 2(i), p. 14 (proof p. 39)

import Mathlib
import Definitions.Def_SustainableFashion_Variety_Setting

namespace SustainableFashion.Variety

theorem proposition_2_i (P : Params)
    (hk : 0 < P.k) (hkk' : P.k < P.k') (hθ : 0 < P.θ) (hn : 0 < P.nbar) (m : ℝ) (hm : P.k' / P.k < m) :
    IsOptimalGiven P m (P.θ / P.k') 0 ∧
    (∀ u q, IsOptimalGiven P m u q → u = P.θ / P.k' ∧ q = 0) ∧
    expProfit P m (P.θ / P.k') 0 =
      P.nbar / 2 * (P.a + P.θ ^ 2 / (2 * P.k') + P.γ / 2 - P.γ / (4 * m)) - P.β * m := by sorry

end SustainableFashion.Variety
