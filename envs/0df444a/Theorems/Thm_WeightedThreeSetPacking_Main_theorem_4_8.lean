-- Prove2me | Theorems.Thm_WeightedThreeSetPacking_Main_theorem_4_8
-- name    : WeightedThreeSetPacking.Main.theorem_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:26.310056+00:00
-- url     : https://prove2.me/theorems/b49e9509-c59c-44b2-a433-15d58a576519
-- title:
--   Theorem 4.8 — Augmented structural inequality (Tong and Xu, arXiv:2610.10036v1, p. 21)
-- statement:
--   Under the standing setting of Tong and Xu, arXiv:2610.10036v1, Theorem 4.8, p. 21, use the inclusive neighborhoods, claws and exact parameters defined above.
--
--   For the Phase I packing $A$ and every optimum $O$, $$2w(O)\le(4-c)w(A)+aG(A,O)=3.3816w(A)+0.5433G(A,O).$$ No covering construction or component certificate is an assumption of this theorem.
--
--   This result provides the corresponding source statement in the dependency chain for the full approximation theorem.
--
--   Differences from the source:
--   - generalization: Positive rational set weights, an optimum packing O, and its rank-three conflict graph (or an analysis lift). → Positive real weights on A∪O, independent O, and finite graphs with the inherited two-sided inclusive degree bounds and maximum-neighbor assignment.; reason: These inequalities use positivity, independence and the rank-three degree bounds; every source instance and its weight-preserving lift satisfies these assumptions.
--   - encoding: Finite set families, inclusive neighborhoods, witnessed exchange multiarcs and finite sums. → Finite carrier types and Finsets, with one triple per witnessed arc and inclusive neighborhoods.; reason: This preserves common vertices, distinct-neighbor sums and incidence multiplicities.
--   - generalization: The original Phase I output A. → Every A satisfying the bounded square local optimality condition of Phase I.; reason: The structural analysis uses the resulting local optimality, not the particular improving path or greedy tie order.
-- source:
--   Tong and Xu, arXiv:2610.10036v1, Theorem 4.8, p. 21; https://arxiv.org/abs/2610.10036v1

import Definitions.Def_WeightedThreeSetPacking_Main_Analysis

namespace WeightedThreeSetPacking.Main

open scoped BigOperators

/-- Tong and Xu, arXiv:2610.10036v1, Theorem 4.8, p. 21. -/
theorem theorem_4_8 {V : Type} [Fintype V] [DecidableEq V] (D : Analysis V)
    (hvalid : ValidAnalysis D)
    (hlocal : SquareLocal D s₀) :
    2 * mass D D.O ≤ (4-c)*mass D D.A + a*residualTotal D ∧
    (4-c)*mass D D.A + a*residualTotal D =
      (4227/1250 : ℝ)*mass D D.A + (5433/10000 : ℝ)*residualTotal D := by sorry

end WeightedThreeSetPacking.Main
