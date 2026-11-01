-- Prove2me | Theorems.Thm_WagerFairDiv_theorem_2_ir_of_proportional
-- name    : WagerFairDiv.theorem_2_ir_of_proportional
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:15:44.321843+00:00
-- url     : https://prove2.me/theorems/d7909894-3f9d-422c-9ff3-06338209dc9e
-- title:
--   Proof of Theorem 2 (A.2, p.13), second half — proportionality gives individual rationality (no IC needed)
-- statement:
--   There are $n$ agents (bettors) and $m$ divisible goods (outcomes). A report profile $\hat{\mathbf v}=(\hat{\mathbf v}_1,\dots,\hat{\mathbf v}_n)$ (written $\hat{\mathbf p}$ on the wagering side) assigns to every agent a point of the probability simplex $\Delta_m=\{x\in\mathbb R^m: x_j\ge0,\ \sum_j x_j=1\}$, and $\mathbf e$ (weights) or $\mathbf w$ (wagers) is a vector of strictly positive reals, with $E=\sum_i e_i$, $W=\sum_i w_i$. For values $x\in\Delta_m$ and a bundle $z\in\mathbb R^m$, $x(z)=\sum_j x_j z_j$. Mechanisms $\mathcal A,\mathcal B$ map $(\hat{\mathbf v},\mathbf e)$ to numbers $\mathcal A_{i,j}(\hat{\mathbf v},\mathbf e)$; $\mathcal A$ and $\mathcal B$ **correspond** (Definition 10) if $\mathcal B_{i,j}(\hat{\mathbf p},\mathbf w)=W\,\mathcal A_{i,j}(\hat{\mathbf p},\mathbf w)$ for all inputs, $i$ and $j$.
--
--   Let $\mathcal A$ and $\mathcal B$ be corresponding mechanisms. If $\mathcal A$ is proportional, then $\mathcal B$ is individually rational: for every agent $i$ and beliefs $\mathbf p_i\in\Delta_m$ there is a report $\hat{\mathbf p}_i$ (the truthful one works) such that for all $\hat{\mathbf p}_{-i}$ and $\mathbf w$,
--   $$\sum_{j=1}^m p_{i,j}\mathcal B_{i,j}(\hat{\mathbf p},\mathbf w)\ge w_i.$$
--   No incentive compatibility is assumed.
--
--   This is the direction of Theorem 2 that holds for every pair of corresponding mechanisms.
--
--   Differences from the source:
--   - encoding: agents indexed {1, …, n}, goods / outcomes indexed {1, …, m} → Fin n and Fin m, 0-based; reason: Lean convention; agent 1 of the paper is index 0, no instance changes
--   - reading: reported values v̂ᵢ and reports p̂ᵢ are not given a domain in the text → every report, true value and belief is a point of stdSimplex ℝ (Fin m) (nonnegative, summing to 1); reason: Definition 10 feeds the same (p̂, w) to A and B, true values are normalized (p.2) and beliefs are probabilities (p.3), so reports range over the same type space
--   - encoding: weights eᵢ > 0 and wagers wᵢ > 0 → the subtype PosVec n of strictly positive vectors, E = W = PosVec.total; reason: the same instances as the paper's standing assumptions (pp.2–3)
--   - encoding: the profile (vᵢ, v̂₋ᵢ), resp. (pᵢ, p̂₋ᵢ) → Function.update v̂ i vᵢ; reason: the same profile
--   - encoding: IR: there is a report p̂ᵢ such that for all p̂₋ᵢ and w … (Definition 5) → ∃ r, ∀ p̂ w, with agent i's entry of p̂ replaced by r (Function.update); reason: quantifying over full profiles and overwriting entry i is the same as quantifying over p̂₋ᵢ; r depends on i and pᵢ only, as printed
--   - generalization: Theorem 2 assumes A (and B) weakly incentive compatible → no incentive-compatibility hypothesis for this direction; reason: the printed argument of A.2 (p.13) uses only the correspondence and proportionality; the statement specializes to the direction of Theorem 2 by adding the hypothesis
--   - generalization: A a valid allocation mechanism and B a valid wagering mechanism (feasible output, nonnegative security holdings) → A and B arbitrary elements of Mech, with no IsAllocMech or IsWagerMech hypothesis; reason: the argument uses only the correspondence and W > 0; adding the validity hypotheses recovers the printed statement
-- source:
--   Freeman, Pennock & Vaughan, An Equivalence Between Wagering and Fair-Division Mechanisms (preprint, 2018), Appendix A.2 (proof of Theorem 2), p.13, "Next, suppose that A is proportional. Let i ∈ [n], and let p̂i = pi.". PDF sha256 02e3d24f0ced18523a243feb31fc3e2f28997a9d5a723a0137ed0d2320230580

import Mathlib
import Definitions.Def_WagerFairDiv_Model
import Definitions.Def_WagerFairDiv_AllocationProperties
import Definitions.Def_WagerFairDiv_WageringProperties
import Definitions.Def_WagerFairDiv_CorrespondingMechanisms

namespace WagerFairDiv

/-- Freeman, Pennock & Vaughan, *An Equivalence Between Wagering and Fair-Division Mechanisms*
(preprint, 2018), Appendix A.2 (proof of Theorem 2), p.13, second half: "suppose that A is
proportional"; then the corresponding `B` is individually rational (with the truthful report
`p̂ᵢ = pᵢ`). No incentive compatibility is assumed: the printed argument uses none. -/
theorem theorem_2_ir_of_proportional {n m : ℕ} (A B : Mech n m) (hAB : Corresponding A B)
    (hP : Proportional A) : IndivRational B := by sorry

end WagerFairDiv
