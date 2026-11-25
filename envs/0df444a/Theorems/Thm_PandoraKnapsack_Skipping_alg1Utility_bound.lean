-- Prove2me | Theorems.Thm_PandoraKnapsack_Skipping_alg1Utility_bound
-- name    : PandoraKnapsack.Skipping.alg1Utility_bound
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T17:24:46.44062+00:00
-- url     : https://prove2.me/theorems/80cb131c-cd3e-57c6-af34-eb58996f35ad
-- title:
--   Algorithm 1 earns an eighth of the payoff of any profitable feasible LP solution
-- statement:
--   For any valid instance $I$, let $x$ be a feasible time-indexed LP solution such that each positive coordinate has nonnegative effective reward. The expected utility of Algorithm 1 satisfies
--   $$U_I(x)\ge\operatorname{obj}(x)/8.$$
--
--   This guarantee applies to sparse approximate solutions and includes the cost of a failed attempt.
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen, Pandora’s Knapsack via Simple Policies, arXiv:2509.05956v5, https://arxiv.org/html/2509.05956v5#S5.SS1, Algorithm 1 and proof of Theorem 5.1. Derived feasible-input formulation.

import Definitions.Def_PandoraKnapsack_Skipping_RoundingPayoff

open MeasureTheory

namespace PandoraKnapsack.Skipping

theorem alg1Utility_bound {n m T : ℕ} (I : Instance n m T) (hI : IsValid I) (x : LPArray n m)
    (hx : PsiFeasible I T x)
    (hsupp : ∀ i j t, t ≤ T → 0 < x i j t → 0 ≤ effWeight I i j t) :
    psiObjective I T x / 8 ≤ alg1Utility I x := by sorry

end PandoraKnapsack.Skipping
