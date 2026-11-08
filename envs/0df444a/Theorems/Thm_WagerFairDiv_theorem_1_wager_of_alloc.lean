-- Prove2me | Theorems.Thm_WagerFairDiv_theorem_1_wager_of_alloc
-- name    : WagerFairDiv.theorem_1_wager_of_alloc
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T09:15:52.187808+00:00
-- url     : https://prove2.me/theorems/dead737a-f5ca-457f-bcd3-6037e45bc33c
-- title:
--   Proof of Theorem 1 (A.1, p.12), second half — IC of the allocation mechanism gives IC of the wagering mechanism
-- statement:
--   There are $n$ agents (bettors) and $m$ divisible goods (outcomes). A report profile $\hat{\mathbf v}=(\hat{\mathbf v}_1,\dots,\hat{\mathbf v}_n)$ (written $\hat{\mathbf p}$ on the wagering side) assigns to every agent a point of the probability simplex $\Delta_m=\{x\in\mathbb R^m: x_j\ge0,\ \sum_j x_j=1\}$, and $\mathbf e$ (weights) or $\mathbf w$ (wagers) is a vector of strictly positive reals, with $E=\sum_i e_i$, $W=\sum_i w_i$. For values $x\in\Delta_m$ and a bundle $z\in\mathbb R^m$, $x(z)=\sum_j x_j z_j$. Mechanisms $\mathcal A,\mathcal B$ map $(\hat{\mathbf v},\mathbf e)$ to numbers $\mathcal A_{i,j}(\hat{\mathbf v},\mathbf e)$; $\mathcal A$ and $\mathcal B$ **correspond** (Definition 10) if $\mathcal B_{i,j}(\hat{\mathbf p},\mathbf w)=W\,\mathcal A_{i,j}(\hat{\mathbf p},\mathbf w)$ for all inputs, $i$ and $j$.
--
--   Let $\mathcal A$ and $\mathcal B$ be corresponding mechanisms.
--
--   1. If $\mathcal A$ is weakly incentive compatible, then $\mathcal B$ is weakly incentive compatible.
--   2. If $\mathcal A$ is strictly incentive compatible, then $\mathcal B$ is strictly incentive compatible.
--
--   Together with the first half, this gives Theorem 1.
--
--   Differences from the source:
--   - encoding: agents indexed {1, …, n}, goods / outcomes indexed {1, …, m} → Fin n and Fin m, 0-based; reason: Lean convention; agent 1 of the paper is index 0, no instance changes
--   - reading: reported values v̂ᵢ and reports p̂ᵢ are not given a domain in the text → every report, true value and belief is a point of stdSimplex ℝ (Fin m) (nonnegative, summing to 1); reason: Definition 10 feeds the same (p̂, w) to A and B, true values are normalized (p.2) and beliefs are probabilities (p.3), so reports range over the same type space
--   - encoding: weights eᵢ > 0 and wagers wᵢ > 0 → the subtype PosVec n of strictly positive vectors, E = W = PosVec.total; reason: the same instances as the paper's standing assumptions (pp.2–3)
--   - encoding: the profile (vᵢ, v̂₋ᵢ), resp. (pᵢ, p̂₋ᵢ) → Function.update v̂ i vᵢ; reason: the same profile
--   - encoding: strictly incentive compatible: "this inequality is strict whenever vᵢ ≠ v̂ᵢ" (Definitions 4, 7) → weak IC together with the strict inequality for every report vᵢ ≠ v̂ᵢ; reason: at vᵢ = v̂ᵢ both sides coincide, so the conjunction holds for exactly the same mechanisms
--   - generalization: A a valid allocation mechanism and B a valid wagering mechanism (feasible output, nonnegative security holdings) → A and B arbitrary elements of Mech, with no IsAllocMech or IsWagerMech hypothesis; reason: the argument uses only the correspondence and W > 0; adding the validity hypotheses recovers the printed statement
-- source:
--   Freeman, Pennock & Vaughan, An Equivalence Between Wagering and Fair-Division Mechanisms (preprint, 2018), Appendix A.1 (proof of Theorem 1), p.12, "Next, suppose that A is weakly incentive compatible … Once again if A is strictly incentive compatible then the inequality is strict, implying that B is strictly incentive compatible.". PDF sha256 02e3d24f0ced18523a243feb31fc3e2f28997a9d5a723a0137ed0d2320230580

import Mathlib
import Definitions.Def_WagerFairDiv_Model
import Definitions.Def_WagerFairDiv_AllocationProperties
import Definitions.Def_WagerFairDiv_WageringProperties
import Definitions.Def_WagerFairDiv_CorrespondingMechanisms

namespace WagerFairDiv

/-- Freeman, Pennock & Vaughan, *An Equivalence Between Wagering and Fair-Division Mechanisms*
(preprint, 2018), Appendix A.1 (proof of Theorem 1), p.12, second half: if `A` is weakly incentive
compatible then so is the corresponding `B`, and "if A is strictly incentive compatible then the
inequality is strict, implying that B is strictly incentive compatible". -/
theorem theorem_1_wager_of_alloc {n m : ℕ} (A B : Mech n m) (hAB : Corresponding A B) :
    (AllocWeakIC A → WagerWeakIC B) ∧ (AllocStrictIC A → WagerStrictIC B) := by sorry

end WagerFairDiv
