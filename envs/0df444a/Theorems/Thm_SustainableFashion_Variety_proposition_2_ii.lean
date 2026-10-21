-- Prove2me | Theorems.Thm_SustainableFashion_Variety_proposition_2_ii
-- name    : SustainableFashion.Variety.proposition_2_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:40.235913+00:00
-- url     : https://prove2.me/theorems/4ad4ecaf-7345-4a07-ae20-1206af86b9d7
-- title:
--   Proposition 2(ii), p. 15 — for m ≤ k′/k: û = θk′/(mk(2k′ − mk)), q̂ = n̄(1 − mk/k′) and the profit value
-- statement:
--   Fix parameters with $0<k<k'$, $\theta>0$ and $\bar n>0$, and a number of styles $1\le m\le k'/k$. Then the pair
--   $$\hat u=\frac{\theta k'}{mk(2k'-mk)},\qquad \hat q=\bar n\Big(1-\frac{mk}{k'}\Big)$$
--   maximises the expected profit (1) over quality $u\ge0$ and inventory $0\le q\le\bar n$, it is the only maximiser, and the maximal expected profit is
--   $$\mathbb E\Pi=\bar n\Big(\frac a2+\frac{\theta^2k'}{4mk(2k'-mk)}-\frac{\gamma}{8m}+\frac\gamma4\Big)-\beta m .$$
--
--   With few styles the firm stocks some inventory before the season and uses quick response for the excess demand.
--
--   **Formalization Note** No sign condition on $\beta$, $\gamma$ or $a$ is assumed: for a given $m$ they enter (1) only additively, as on the page. The hypothesis $\theta>0$ (consumers value quality) is what makes the maximiser unique; at $\theta=0$ the optimal quality is $0$ and every inventory is optimal.
-- source:
--   Long & Nasiry, Sustainability in the Fast Fashion Industry, SSRN 3486502 author's manuscript (2021; MSOM doi:10.1287/msom.2021.1054), Proposition 2(ii), p. 15 (proof p. 39)

import Mathlib
import Definitions.Def_SustainableFashion_Variety_Setting

namespace SustainableFashion.Variety

theorem proposition_2_ii (P : Params)
    (hk : 0 < P.k) (hkk' : P.k < P.k') (hθ : 0 < P.θ) (hn : 0 < P.nbar) (m : ℝ) (hm1 : 1 ≤ m)
    (hm : m ≤ P.k' / P.k) :
    IsOptimalGiven P m (P.θ * P.k' / (m * P.k * (2 * P.k' - m * P.k)))
        (P.nbar * (1 - m * P.k / P.k')) ∧
    (∀ u q, IsOptimalGiven P m u q →
        u = P.θ * P.k' / (m * P.k * (2 * P.k' - m * P.k)) ∧ q = P.nbar * (1 - m * P.k / P.k')) ∧
    expProfit P m (P.θ * P.k' / (m * P.k * (2 * P.k' - m * P.k))) (P.nbar * (1 - m * P.k / P.k')) =
      P.nbar * (P.a / 2 + P.θ ^ 2 * P.k' / (4 * m * P.k * (2 * P.k' - m * P.k))
        - P.γ / (8 * m) + P.γ / 4) - P.β * m := by sorry

end SustainableFashion.Variety
