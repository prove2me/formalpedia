-- Prove2me | Theorems.Thm_WagerFairDiv_theorem_2
-- name    : WagerFairDiv.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:16:06.483137+00:00
-- url     : https://prove2.me/theorems/d30df9d3-6f16-49b0-b86b-e37806fd8893
-- title:
--   Theorem 2, p.5 — a weakly IC allocation mechanism is proportional iff its corresponding wagering mechanism is individually rational
-- statement:
--   There are $n$ agents (bettors) and $m$ divisible goods (outcomes). A report profile $\hat{\mathbf v}=(\hat{\mathbf v}_1,\dots,\hat{\mathbf v}_n)$ (written $\hat{\mathbf p}$ on the wagering side) assigns to every agent a point of the probability simplex $\Delta_m=\{x\in\mathbb R^m: x_j\ge0,\ \sum_j x_j=1\}$, and $\mathbf e$ (weights) or $\mathbf w$ (wagers) is a vector of strictly positive reals, with $E=\sum_i e_i$, $W=\sum_i w_i$. For values $x\in\Delta_m$ and a bundle $z\in\mathbb R^m$, $x(z)=\sum_j x_j z_j$. Mechanisms $\mathcal A,\mathcal B$ map $(\hat{\mathbf v},\mathbf e)$ to numbers $\mathcal A_{i,j}(\hat{\mathbf v},\mathbf e)$; $\mathcal A$ and $\mathcal B$ **correspond** (Definition 10) if $\mathcal B_{i,j}(\hat{\mathbf p},\mathbf w)=W\,\mathcal A_{i,j}(\hat{\mathbf p},\mathbf w)$ for all inputs, $i$ and $j$.
--
--   Let $\mathcal A$ and $\mathcal B$ be corresponding mechanisms, and let $\mathcal A$ be weakly incentive compatible (equivalently, by Theorem 1, $\mathcal B$ is). Then
--   $$\mathcal A\text{ is proportional}\iff\mathcal B\text{ is individually rational}.$$
--
--   Individual rationality of a wager is a "fair share" guarantee of the collected wagers. The IC hypothesis bridges reported values (proportionality) and true beliefs (individual rationality).
--
--   Differences from the source:
--   - encoding: agents indexed {1, …, n}, goods / outcomes indexed {1, …, m} → Fin n and Fin m, 0-based; reason: Lean convention; agent 1 of the paper is index 0, no instance changes
--   - reading: reported values v̂ᵢ and reports p̂ᵢ are not given a domain in the text → every report, true value and belief is a point of stdSimplex ℝ (Fin m) (nonnegative, summing to 1); reason: Definition 10 feeds the same (p̂, w) to A and B, true values are normalized (p.2) and beliefs are probabilities (p.3), so reports range over the same type space
--   - encoding: weights eᵢ > 0 and wagers wᵢ > 0 → the subtype PosVec n of strictly positive vectors, E = W = PosVec.total; reason: the same instances as the paper's standing assumptions (pp.2–3)
--   - encoding: the profile (vᵢ, v̂₋ᵢ), resp. (pᵢ, p̂₋ᵢ) → Function.update v̂ i vᵢ; reason: the same profile
--   - encoding: IR: there is a report p̂ᵢ such that for all p̂₋ᵢ and w … (Definition 5) → ∃ r, ∀ p̂ w, with agent i's entry of p̂ replaced by r (Function.update); reason: quantifying over full profiles and overwriting entry i is the same as quantifying over p̂₋ᵢ; r depends on i and pᵢ only, as printed
--   - reading: "random assignment mechanism" (Theorems 1–3, p.5) → an allocation mechanism of §2.1 (a Mech; validity IsAllocMech where needed); reason: the term is never defined in the paper and is a leftover name for the allocation mechanisms of §2.1, which Definition 10 pairs with wagering mechanisms
--   - encoding: "A (weakly) incentive compatible … A is proportional iff the corresponding (weakly) incentive compatible wagering mechanism B is individually rational" → the single hypothesis AllocWeakIC A; reason: for corresponding mechanisms weak IC of A is equivalent to weak IC of B (Theorem 1), so the hypotheses select the same pairs
--   - generalization: A a valid allocation mechanism and B a valid wagering mechanism (feasible output, nonnegative security holdings) → A and B arbitrary elements of Mech, with no IsAllocMech or IsWagerMech hypothesis; reason: the argument uses only the correspondence and W > 0; adding the validity hypotheses recovers the printed statement
-- source:
--   Freeman, Pennock & Vaughan, An Equivalence Between Wagering and Fair-Division Mechanisms (preprint, 2018), Theorem 2, §3.1, p.5 (proof: Appendix A.2, p.13). PDF sha256 02e3d24f0ced18523a243feb31fc3e2f28997a9d5a723a0137ed0d2320230580

import Mathlib
import Definitions.Def_WagerFairDiv_Model
import Definitions.Def_WagerFairDiv_AllocationProperties
import Definitions.Def_WagerFairDiv_WageringProperties
import Definitions.Def_WagerFairDiv_CorrespondingMechanisms

namespace WagerFairDiv

/-- Freeman, Pennock & Vaughan, *An Equivalence Between Wagering and Fair-Division Mechanisms*
(preprint, 2018), Theorem 2, p.5: a (weakly) incentive compatible allocation ("random assignment")
mechanism `A` is proportional if and only if the corresponding wagering mechanism `B` is
individually rational.

**Formalization Note.** The incentive-compatibility hypothesis is put on `A`; by Theorem 1 it is
equivalent to weak incentive compatibility of `B`, which the paper also names. -/
theorem theorem_2 {n m : ℕ} (A B : Mech n m) (hAB : Corresponding A B) (hIC : AllocWeakIC A) :
    Proportional A ↔ IndivRational B := by sorry

end WagerFairDiv
