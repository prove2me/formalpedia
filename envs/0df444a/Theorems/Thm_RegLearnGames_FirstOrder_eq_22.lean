-- Prove2me | Theorems.Thm_RegLearnGames_FirstOrder_eq_22
-- name    : RegLearnGames.FirstOrder.eq_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:44:43.384986+00:00
-- url     : https://prove2.me/theorems/2fcfc862-2001-420b-b6ff-3bbf494f4805
-- title:
--   Equation (22), supp. p. 10 — aggregate first-order regret bound
-- statement:
--   Consider $n$ players with $d\ge1$ strategies each and costs in $[0,1]$. Let $w^t$ be a mixed profile at each round through $T$. Suppose every player satisfies the first-order bound (21) with constants $A_1\ge0$ and $A_2$. For any fixed pure profile $s^*$, write $P=\sum_{t=1}^T\sum_i c^t_{i,s_i^*}$. Then
--   $$\sum_{t=1}^T C(w^t)\le P+A_1\sqrt{n\log d}\sqrt P+A_2n\log d.$$
--
--   This is the aggregate cost bound before the smoothness condition is used.
--
--   **Formalization Note** The source's Cauchy–Schwarz step requires $A_1\ge0$, stated explicitly here. The printed final sum in (22) uses $T$ as both bound and index; the index is read as $t$. The $log$ is natural logarithm.
-- source:
--   Syrgkanis, Agarwal, Luo, Schapire, Fast Convergence of Regularized Learning in Games, arXiv:1507.00407v5, supp. p. 10 (PDF p. 19), equation (22)

import Mathlib
import Definitions.Def_RegLearnGames_FirstOrder_Setting

namespace RegLearnGames.FirstOrder

open Finset

/-- The final line of display (22), after the sum over players. -/
theorem eq_22 {n d : ℕ} [NeZero d]
    (c : Fin n → (Fin n → Fin d) → ℝ)
    (hc : ∀ i s, c i s ∈ Set.Icc (0 : ℝ) 1)
    (w : ℕ → Fin n → Fin d → ℝ) (T : ℕ)
    (hw : ∀ t ∈ Finset.Icc 1 T, AGT.IsMixedProfile (w t))
    (A₁ A₂ : ℝ) (hA₁ : 0 ≤ A₁)
    (hreg : HasFirstOrderRegret c w T A₁ A₂)
    (sstar : Fin n → Fin d) :
    (∑ t ∈ Finset.Icc 1 T, socialCost c (w t)) ≤
      (∑ t ∈ Finset.Icc 1 T, ∑ i, costVec c (w t) i (sstar i)) +
        A₁ * Real.sqrt ((n : ℝ) * Real.log (d : ℝ)) *
          Real.sqrt (∑ t ∈ Finset.Icc 1 T,
            ∑ i, costVec c (w t) i (sstar i)) +
        A₂ * (n : ℝ) * Real.log (d : ℝ) := by sorry

end RegLearnGames.FirstOrder
