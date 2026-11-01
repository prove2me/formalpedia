-- Prove2me | Theorems.Thm_WagerFairDiv_theorem_2_proportional_of_ir
-- name    : WagerFairDiv.theorem_2_proportional_of_ir
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:15:59.462985+00:00
-- url     : https://prove2.me/theorems/f174c6a3-1b41-41e7-862b-2f10b222974e
-- title:
--   Proof of Theorem 2 (A.2, p.13), first half — individual rationality and weak IC of the wagering mechanism give proportionality
-- statement:
--   There are $n$ agents (bettors) and $m$ divisible goods (outcomes). A report profile $\hat{\mathbf v}=(\hat{\mathbf v}_1,\dots,\hat{\mathbf v}_n)$ (written $\hat{\mathbf p}$ on the wagering side) assigns to every agent a point of the probability simplex $\Delta_m=\{x\in\mathbb R^m: x_j\ge0,\ \sum_j x_j=1\}$, and $\mathbf e$ (weights) or $\mathbf w$ (wagers) is a vector of strictly positive reals, with $E=\sum_i e_i$, $W=\sum_i w_i$. For values $x\in\Delta_m$ and a bundle $z\in\mathbb R^m$, $x(z)=\sum_j x_j z_j$. Mechanisms $\mathcal A,\mathcal B$ map $(\hat{\mathbf v},\mathbf e)$ to numbers $\mathcal A_{i,j}(\hat{\mathbf v},\mathbf e)$; $\mathcal A$ and $\mathcal B$ **correspond** (Definition 10) if $\mathcal B_{i,j}(\hat{\mathbf p},\mathbf w)=W\,\mathcal A_{i,j}(\hat{\mathbf p},\mathbf w)$ for all inputs, $i$ and $j$.
--
--   Let $\mathcal A$ and $\mathcal B$ be corresponding mechanisms. If $\mathcal B$ is individually rational and weakly incentive compatible, then $\mathcal A$ is proportional: for all $\hat{\mathbf v}$, $\mathbf e$ and $i$,
--   $$\hat v_i\big(\mathcal A_i(\hat{\mathbf v},\mathbf e)\big)\ge\frac{e_i}{E}.$$
--
--   Individual rationality guarantees a good report; weak incentive compatibility makes the truthful report at least as good, which is what proportionality (stated with reported values) needs.
--
--   Differences from the source:
--   - encoding: agents indexed {1, …, n}, goods / outcomes indexed {1, …, m} → Fin n and Fin m, 0-based; reason: Lean convention; agent 1 of the paper is index 0, no instance changes
--   - reading: reported values v̂ᵢ and reports p̂ᵢ are not given a domain in the text → every report, true value and belief is a point of stdSimplex ℝ (Fin m) (nonnegative, summing to 1); reason: Definition 10 feeds the same (p̂, w) to A and B, true values are normalized (p.2) and beliefs are probabilities (p.3), so reports range over the same type space
--   - encoding: weights eᵢ > 0 and wagers wᵢ > 0 → the subtype PosVec n of strictly positive vectors, E = W = PosVec.total; reason: the same instances as the paper's standing assumptions (pp.2–3)
--   - encoding: the profile (vᵢ, v̂₋ᵢ), resp. (pᵢ, p̂₋ᵢ) → Function.update v̂ i vᵢ; reason: the same profile
--   - encoding: IR: there is a report p̂ᵢ such that for all p̂₋ᵢ and w … (Definition 5) → ∃ r, ∀ p̂ w, with agent i's entry of p̂ replaced by r (Function.update); reason: quantifying over full profiles and overwriting entry i is the same as quantifying over p̂₋ᵢ; r depends on i and pᵢ only, as printed
--   - generalization: A a valid allocation mechanism and B a valid wagering mechanism (feasible output, nonnegative security holdings) → A and B arbitrary elements of Mech, with no IsAllocMech or IsWagerMech hypothesis; reason: the argument uses only the correspondence and W > 0; adding the validity hypotheses recovers the printed statement
-- source:
--   Freeman, Pennock & Vaughan, An Equivalence Between Wagering and Fair-Division Mechanisms (preprint, 2018), Appendix A.2 (proof of Theorem 2), p.13, "First, suppose that B is individually rational and weakly incentive compatible.". PDF sha256 02e3d24f0ced18523a243feb31fc3e2f28997a9d5a723a0137ed0d2320230580

import Mathlib
import Definitions.Def_WagerFairDiv_Model
import Definitions.Def_WagerFairDiv_AllocationProperties
import Definitions.Def_WagerFairDiv_WageringProperties
import Definitions.Def_WagerFairDiv_CorrespondingMechanisms

namespace WagerFairDiv

/-- Freeman, Pennock & Vaughan, *An Equivalence Between Wagering and Fair-Division Mechanisms*
(preprint, 2018), Appendix A.2 (proof of Theorem 2), p.13, first half: "suppose that B is individually
rational and weakly incentive compatible"; then the corresponding `A` is proportional. -/
theorem theorem_2_proportional_of_ir {n m : ℕ} (A B : Mech n m) (hAB : Corresponding A B)
    (hIR : IndivRational B) (hIC : WagerWeakIC B) : Proportional A := by sorry

end WagerFairDiv
