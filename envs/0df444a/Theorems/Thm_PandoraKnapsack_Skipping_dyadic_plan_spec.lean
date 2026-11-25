-- Prove2me | Theorems.Thm_PandoraKnapsack_Skipping_dyadic_plan_spec
-- name    : PandoraKnapsack.Skipping.dyadic_plan_spec
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T17:35:04.433969+00:00
-- url     : https://prove2.me/theorems/2feec957-1726-502e-82e2-9198db63233a
-- title:
--   Sparse LP approximation with profitable support
-- statement:
--   For every valid stochastic knapsack instance, the computed dyadic plan $y$ is feasible in the original time-indexed LP, has nonnegative effective reward on each positive coordinate, and for every feasible $z$ supported at dyadic times and zero satisfies
--   $$\operatorname{obj}(z)\le2\operatorname{obj}(y).$$
--   This is the normalized packing guarantee after converting the LP rows back into original units.
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen, Pandora’s Knapsack via Simple Policies, arXiv:2509.05956v5, https://arxiv.org/html/2509.05956v5#A2.SS1, Appendix B.1 and Theorem 5.1. Constructive variant on the unshifted dyadic subgrid, using the bounded projected-row packing algorithm.

import Definitions.Def_PandoraKnapsack_Skipping_DyadicPlan

open MeasureTheory

namespace PandoraKnapsack.Skipping

theorem dyadic_plan_spec {n m T : ℕ} (I : Instance n m T) (hI : IsValid I) :
    PsiFeasible I T (dyadicPlan I) ∧
    (∀ i j t, 0 < dyadicPlan I i j t → 0 ≤ effWeight I i j t) ∧
    ∀ z, PsiFeasible I T z → (∀ i j t, t ∉ breakpoints T → z i j t = 0) →
      psiObjective I T z ≤ 2 * psiObjective I T (dyadicPlan I) := by sorry

end PandoraKnapsack.Skipping
