-- Prove2me | Theorems.Thm_WagerFairDiv_theorem_3_sideBetPO_of_pareto
-- name    : WagerFairDiv.theorem_3_sideBetPO_of_pareto
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T09:15:57.195859+00:00
-- url     : https://prove2.me/theorems/9562de97-c582-48ad-885c-c177e759333f
-- title:
--   Proof of Theorem 3 (A.3, pp.13–14), "only if", first step — Pareto optimality gives side-bet Pareto optimality
-- statement:
--   There are $n$ agents (bettors) and $m$ divisible goods (outcomes). A report profile $\hat{\mathbf v}=(\hat{\mathbf v}_1,\dots,\hat{\mathbf v}_n)$ (written $\hat{\mathbf p}$ on the wagering side) assigns to every agent a point of the probability simplex $\Delta_m=\{x\in\mathbb R^m: x_j\ge0,\ \sum_j x_j=1\}$, and $\mathbf e$ (weights) or $\mathbf w$ (wagers) is a vector of strictly positive reals, with $E=\sum_i e_i$, $W=\sum_i w_i$. For values $x\in\Delta_m$ and a bundle $z\in\mathbb R^m$, $x(z)=\sum_j x_j z_j$. Mechanisms $\mathcal A,\mathcal B$ map $(\hat{\mathbf v},\mathbf e)$ to numbers $\mathcal A_{i,j}(\hat{\mathbf v},\mathbf e)$; $\mathcal A$ and $\mathcal B$ **correspond** (Definition 10) if $\mathcal B_{i,j}(\hat{\mathbf p},\mathbf w)=W\,\mathcal A_{i,j}(\hat{\mathbf p},\mathbf w)$ for all inputs, $i$ and $j$.
--
--   Let $\mathcal A$ be a valid allocation mechanism and $\mathcal B$ its corresponding wagering mechanism. If $\mathcal A$ is Pareto optimal, then $\mathcal B$ is side-bet Pareto optimal: for no $\hat{\mathbf p}$, $\mathbf w$ is there a profitable side bet $\Delta\mathbf b$ for the allocation $\mathcal B(\hat{\mathbf p},\mathbf w)$.
--
--   A profitable side bet would turn into a Pareto improvement of $\mathcal A(\hat{\mathbf p},\mathbf w)$.
--
--   Differences from the source:
--   - encoding: agents indexed {1, …, n}, goods / outcomes indexed {1, …, m} → Fin n and Fin m, 0-based; reason: Lean convention; agent 1 of the paper is index 0, no instance changes
--   - reading: reported values v̂ᵢ and reports p̂ᵢ are not given a domain in the text → every report, true value and belief is a point of stdSimplex ℝ (Fin m) (nonnegative, summing to 1); reason: Definition 10 feeds the same (p̂, w) to A and B, true values are normalized (p.2) and beliefs are probabilities (p.3), so reports range over the same type space
--   - encoding: weights eᵢ > 0 and wagers wᵢ > 0 → the subtype PosVec n of strictly positive vectors, E = W = PosVec.total; reason: the same instances as the paper's standing assumptions (pp.2–3)
--   - encoding: A "outputs a feasible allocation" (standing assumption of §2.1, p.2) → explicit hypothesis IsAllocMech A; reason: the paper's definition of an allocation mechanism; the Lean type Mech does not carry it
--   - reading: Pareto optimality over "all alternative allocations" (Definition 3) → alternatives a′ range over feasible allocations (a′ᵢⱼ ≥ 0, Σᵢ a′ᵢⱼ ≤ 1); reason: §2.1, p.2 defines allocations as feasible ones; over infeasible alternatives no mechanism would be Pareto optimal
--   - encoding: Definition 8, condition 2: minⱼ (bᵢⱼ + Δbᵢⱼ) ≥ 0 → 0 ≤ bᵢⱼ + Δbᵢⱼ for all i, j; reason: equivalent for m ≥ 1; for m = 0 there are no profiles, since the simplex over Fin 0 is empty
-- source:
--   Freeman, Pennock & Vaughan, An Equivalence Between Wagering and Fair-Division Mechanisms (preprint, 2018), Appendix A.3 (proof of Theorem 3), pp.13–14, "We prove the "only if" direction first. Suppose that B is not side-bet Pareto optimal." … "Therefore, A is mot Pareto optimal.". PDF sha256 02e3d24f0ced18523a243feb31fc3e2f28997a9d5a723a0137ed0d2320230580

import Mathlib
import Definitions.Def_WagerFairDiv_Model
import Definitions.Def_WagerFairDiv_AllocationProperties
import Definitions.Def_WagerFairDiv_WageringProperties
import Definitions.Def_WagerFairDiv_CorrespondingMechanisms

namespace WagerFairDiv

/-- Freeman, Pennock & Vaughan, *An Equivalence Between Wagering and Fair-Division Mechanisms*
(preprint, 2018), Appendix A.3 (proof of Theorem 3), pp.13–14, "only if" direction, first step: if the
(valid) allocation mechanism `A` is Pareto optimal, the corresponding wagering mechanism `B` is
side-bet Pareto optimal (a profitable side bet `Δb` would give the Pareto-improving allocation
`aᵢ,ⱼ = (Bᵢ,ⱼ(p̂, w) + Δbᵢ,ⱼ) / W`). -/
theorem theorem_3_sideBetPO_of_pareto {n m : ℕ} (A B : Mech n m) (hA : IsAllocMech A)
    (hAB : Corresponding A B) (hPO : ParetoOptimal A) : SideBetPO B := by sorry

end WagerFairDiv
