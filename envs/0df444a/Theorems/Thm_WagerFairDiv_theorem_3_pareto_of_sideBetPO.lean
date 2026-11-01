-- Prove2me | Theorems.Thm_WagerFairDiv_theorem_3_pareto_of_sideBetPO
-- name    : WagerFairDiv.theorem_3_pareto_of_sideBetPO
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:16:13.157531+00:00
-- url     : https://prove2.me/theorems/336d34df-6518-46a3-b088-e71d032c63d5
-- title:
--   Proof of Theorem 3 (A.3, p.14), "if" direction — side-bet Pareto optimality and budget balance give Pareto optimality
-- statement:
--   There are $n$ agents (bettors) and $m$ divisible goods (outcomes). A report profile $\hat{\mathbf v}=(\hat{\mathbf v}_1,\dots,\hat{\mathbf v}_n)$ (written $\hat{\mathbf p}$ on the wagering side) assigns to every agent a point of the probability simplex $\Delta_m=\{x\in\mathbb R^m: x_j\ge0,\ \sum_j x_j=1\}$, and $\mathbf e$ (weights) or $\mathbf w$ (wagers) is a vector of strictly positive reals, with $E=\sum_i e_i$, $W=\sum_i w_i$. For values $x\in\Delta_m$ and a bundle $z\in\mathbb R^m$, $x(z)=\sum_j x_j z_j$. Mechanisms $\mathcal A,\mathcal B$ map $(\hat{\mathbf v},\mathbf e)$ to numbers $\mathcal A_{i,j}(\hat{\mathbf v},\mathbf e)$; $\mathcal A$ and $\mathcal B$ **correspond** (Definition 10) if $\mathcal B_{i,j}(\hat{\mathbf p},\mathbf w)=W\,\mathcal A_{i,j}(\hat{\mathbf p},\mathbf w)$ for all inputs, $i$ and $j$.
--
--   Let $\mathcal A$ be a valid allocation mechanism and $\mathcal B$ its corresponding wagering mechanism. Suppose $\mathcal B$ is side-bet Pareto optimal and budget balanced on reported support: $\sum_i\mathcal B_{i,j}(\hat{\mathbf p},\mathbf w)=W$ whenever $\hat p_{k,j}>0$ for some $k$. Then $\mathcal A$ is Pareto optimal.
--
--   Strict budget balance implies the budget-balance hypothesis used here, so this statement contains the printed "if" direction of Theorem 3.
--
--   Differences from the source:
--   - encoding: agents indexed {1, …, n}, goods / outcomes indexed {1, …, m} → Fin n and Fin m, 0-based; reason: Lean convention; agent 1 of the paper is index 0, no instance changes
--   - reading: reported values v̂ᵢ and reports p̂ᵢ are not given a domain in the text → every report, true value and belief is a point of stdSimplex ℝ (Fin m) (nonnegative, summing to 1); reason: Definition 10 feeds the same (p̂, w) to A and B, true values are normalized (p.2) and beliefs are probabilities (p.3), so reports range over the same type space
--   - encoding: weights eᵢ > 0 and wagers wᵢ > 0 → the subtype PosVec n of strictly positive vectors, E = W = PosVec.total; reason: the same instances as the paper's standing assumptions (pp.2–3)
--   - encoding: A "outputs a feasible allocation" (standing assumption of §2.1, p.2) → explicit hypothesis IsAllocMech A; reason: the paper's definition of an allocation mechanism; the Lean type Mech does not carry it
--   - reading: Pareto optimality over "all alternative allocations" (Definition 3) → alternatives a′ range over feasible allocations (a′ᵢⱼ ≥ 0, Σᵢ a′ᵢⱼ ≤ 1); reason: §2.1, p.2 defines allocations as feasible ones; over infeasible alternatives no mechanism would be Pareto optimal
--   - encoding: Definition 8, condition 2: minⱼ (bᵢⱼ + Δbᵢⱼ) ≥ 0 → 0 ≤ bᵢⱼ + Δbᵢⱼ for all i, j; reason: equivalent for m ≥ 1; for m = 0 there are no profiles, since the simplex over Fin 0 is empty
--   - generalization: hypothesis: B strictly budget balanced (Σᵢ Bᵢⱼ = W for every j) → hypothesis BBOnSupport B (Σᵢ Bᵢⱼ = W for every j some agent reports possible); reason: strict budget balance implies BBOnSupport, so this specializes to the printed direction
-- source:
--   Freeman, Pennock & Vaughan, An Equivalence Between Wagering and Fair-Division Mechanisms (preprint, 2018), Appendix A.3 (proof of Theorem 3), p.14, "To prove the "if" direction, suppose that B is side-bet Pareto optimal and strictly budget balanced, but that A is not Pareto optimal.". PDF sha256 02e3d24f0ced18523a243feb31fc3e2f28997a9d5a723a0137ed0d2320230580

import Mathlib
import Definitions.Def_WagerFairDiv_Model
import Definitions.Def_WagerFairDiv_AllocationProperties
import Definitions.Def_WagerFairDiv_WageringProperties
import Definitions.Def_WagerFairDiv_CorrespondingMechanisms

namespace WagerFairDiv

/-- Freeman, Pennock & Vaughan, *An Equivalence Between Wagering and Fair-Division Mechanisms*
(preprint, 2018), Appendix A.3 (proof of Theorem 3), p.14, "if" direction: if `B` is side-bet Pareto
optimal and budget balanced, the corresponding (valid) allocation mechanism `A` is Pareto
optimal.

**Formalization Note.** The printed hypothesis is strict budget balance; here it is the weaker
`BBOnSupport B` (budget balance on every outcome some agent reports possible), so this
statement implies the printed one. -/
theorem theorem_3_pareto_of_sideBetPO {n m : ℕ} (A B : Mech n m) (hA : IsAllocMech A)
    (hAB : Corresponding A B) (hSB : SideBetPO B) (hBB : BBOnSupport B) :
    ParetoOptimal A := by sorry

end WagerFairDiv
