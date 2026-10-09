-- Prove2me | Theorems.Thm_RegLearnGames_FirstOrder_social_cost_eq_sum_inner
-- name    : RegLearnGames.FirstOrder.social_cost_eq_sum_inner
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:45:14.085644+00:00
-- url     : https://prove2.me/theorems/1ec334d9-4a73-47f4-8dc4-dd3d7c8d47ff
-- title:
--   First equality of (22), supp. p. 10 — total expected cost equals the sum of player cost-vector inner products
-- statement:
--   Let $w^1,\ldots,w^T$ be mixed profiles in a finite cost game. With $c_i^t$ the vector of player $i$'s expected cost for each pure strategy against the other players' mixed play,
--   $$\sum_{t=1}^T C(w^t)=\sum_{t=1}^T\sum_i\langle w_i^t,c_i^t\rangle.$$
--
--   This identity converts social cost into the quantities controlled by individual regret bounds.
--
--   **Formalization Note** The expectation uses the product distribution of the players' lotteries. The identity holds for any finite horizon, including $T=0$, when both sums are empty.
-- source:
--   Syrgkanis, Agarwal, Luo, Schapire, Fast Convergence of Regularized Learning in Games, arXiv:1507.00407v5, supp. p. 10 (PDF p. 19), first equality of display (22)

import Mathlib
import Definitions.Def_RegLearnGames_FirstOrder_Setting

namespace RegLearnGames.FirstOrder

open Finset

/-- The first equality in display (22), for the complete time horizon. -/
theorem social_cost_eq_sum_inner {n d : ℕ}
    (c : Fin n → (Fin n → Fin d) → ℝ)
    (w : ℕ → Fin n → Fin d → ℝ) (T : ℕ)
    (hw : ∀ t ∈ Finset.Icc 1 T, AGT.IsMixedProfile (w t)) :
    (∑ t ∈ Finset.Icc 1 T, socialCost c (w t)) =
      ∑ t ∈ Finset.Icc 1 T, ∑ i, (w t i) ⬝ᵥ (costVec c (w t) i) := by sorry

end RegLearnGames.FirstOrder
