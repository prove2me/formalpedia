-- Prove2me | Theorems.Thm_WagerFairDiv_theorem_3
-- name    : WagerFairDiv.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:15:49.711081+00:00
-- url     : https://prove2.me/theorems/91762e0f-03a0-43f8-b07b-290c8278d5c2
-- title:
--   Theorem 3, p.5 (corrected: strict budget balance → budget balance on outcomes some agent reports possible) — Pareto optimality iff side-bet Pareto optimality and budget balance
-- statement:
--   There are $n$ agents (bettors) and $m$ divisible goods (outcomes). A report profile $\hat{\mathbf v}=(\hat{\mathbf v}_1,\dots,\hat{\mathbf v}_n)$ (written $\hat{\mathbf p}$ on the wagering side) assigns to every agent a point of the probability simplex $\Delta_m=\{x\in\mathbb R^m: x_j\ge0,\ \sum_j x_j=1\}$, and $\mathbf e$ (weights) or $\mathbf w$ (wagers) is a vector of strictly positive reals, with $E=\sum_i e_i$, $W=\sum_i w_i$. For values $x\in\Delta_m$ and a bundle $z\in\mathbb R^m$, $x(z)=\sum_j x_j z_j$. Mechanisms $\mathcal A,\mathcal B$ map $(\hat{\mathbf v},\mathbf e)$ to numbers $\mathcal A_{i,j}(\hat{\mathbf v},\mathbf e)$; $\mathcal A$ and $\mathcal B$ **correspond** (Definition 10) if $\mathcal B_{i,j}(\hat{\mathbf p},\mathbf w)=W\,\mathcal A_{i,j}(\hat{\mathbf p},\mathbf w)$ for all inputs, $i$ and $j$.
--
--   Let $\mathcal A$ be a valid allocation mechanism and $\mathcal B$ its corresponding wagering mechanism. Then
--   $$\mathcal A\text{ is Pareto optimal}\iff\mathcal B\text{ is side-bet Pareto optimal and }\sum_{i=1}^n\mathcal B_{i,j}(\hat{\mathbf p},\mathbf w)=W\text{ for all }\hat{\mathbf p},\mathbf w\text{ and every }j\text{ with }\hat p_{k,j}>0\text{ for some }k.$$
--
--   Side-bet Pareto optimality alone lets the principal keep securities; in fair division this is waste. The budget-balance condition forbids waste exactly where it hurts some agent.
--
--   Differences from the source:
--   - encoding: agents indexed {1, …, n}, goods / outcomes indexed {1, …, m} → Fin n and Fin m, 0-based; reason: Lean convention; agent 1 of the paper is index 0, no instance changes
--   - reading: reported values v̂ᵢ and reports p̂ᵢ are not given a domain in the text → every report, true value and belief is a point of stdSimplex ℝ (Fin m) (nonnegative, summing to 1); reason: Definition 10 feeds the same (p̂, w) to A and B, true values are normalized (p.2) and beliefs are probabilities (p.3), so reports range over the same type space
--   - encoding: weights eᵢ > 0 and wagers wᵢ > 0 → the subtype PosVec n of strictly positive vectors, E = W = PosVec.total; reason: the same instances as the paper's standing assumptions (pp.2–3)
--   - encoding: A "outputs a feasible allocation" (standing assumption of §2.1, p.2) → explicit hypothesis IsAllocMech A; reason: the paper's definition of an allocation mechanism; the Lean type Mech does not carry it
--   - reading: Pareto optimality over "all alternative allocations" (Definition 3) → alternatives a′ range over feasible allocations (a′ᵢⱼ ≥ 0, Σᵢ a′ᵢⱼ ≤ 1); reason: §2.1, p.2 defines allocations as feasible ones; over infeasible alternatives no mechanism would be Pareto optimal
--   - encoding: Definition 8, condition 2: minⱼ (bᵢⱼ + Δbᵢⱼ) ≥ 0 → 0 ≤ bᵢⱼ + Δbᵢⱼ for all i, j; reason: equivalent for m ≥ 1; for m = 0 there are no profiles, since the simplex over Fin 0 is empty
--   - reading: "random assignment mechanism" (Theorems 1–3, p.5) → an allocation mechanism of §2.1 (a Mech; validity IsAllocMech where needed); reason: the term is never defined in the paper and is a leftover name for the allocation mechanisms of §2.1, which Definition 10 pairs with wagering mechanisms
--   - correction: A Pareto optimal iff B side-bet Pareto optimal and strictly budget balanced (Σᵢ Bᵢⱼ = W for every j) → A Pareto optimal iff B side-bet Pareto optimal and BBOnSupport B (Σᵢ Bᵢⱼ(p̂, w) = W for every j with p̂ₖⱼ > 0 for some k); reason: the printed "only if" is false: n = 1, m = 2, A₁ⱼ(v̂, e) = 1 if v̂₁ⱼ > 0 else 0 is feasible and Pareto optimal (agent 1 gets value 1, the maximum), yet at v̂₁ = (1, 0) Σᵢ Bᵢ,₂ = 0 < W; strict budget balance implies BBOnSupport, so the printed "if" direction follows from the corrected one
-- source:
--   Freeman, Pennock & Vaughan, An Equivalence Between Wagering and Fair-Division Mechanisms (preprint, 2018), Theorem 3, §3.1, p.5 (proof: Appendix A.3, pp.13–14). PDF sha256 02e3d24f0ced18523a243feb31fc3e2f28997a9d5a723a0137ed0d2320230580

import Mathlib
import Definitions.Def_WagerFairDiv_Model
import Definitions.Def_WagerFairDiv_AllocationProperties
import Definitions.Def_WagerFairDiv_WageringProperties
import Definitions.Def_WagerFairDiv_CorrespondingMechanisms

namespace WagerFairDiv

/-- Freeman, Pennock & Vaughan, *An Equivalence Between Wagering and Fair-Division Mechanisms*
(preprint, 2018), Theorem 3, p.5, **corrected**: a (valid) allocation ("random assignment")
mechanism `A` is Pareto optimal if and only if the corresponding wagering mechanism `B` is
side-bet Pareto optimal and budget balanced on every outcome some agent reports possible.

**Formalization Note.** The printed theorem has "strictly budget balanced"; its "only if" is
false (n = 1, m = 2: give agent 1 every good she reports positive value for; at `v̂₁ = (1, 0)`
good 2 is wasted, yet the mechanism is Pareto optimal). `BBOnSupport` is the minimal
correction; strict budget balance implies it, so the printed "if" direction follows. -/
theorem theorem_3 {n m : ℕ} (A B : Mech n m) (hA : IsAllocMech A) (hAB : Corresponding A B) :
    ParetoOptimal A ↔ SideBetPO B ∧ BBOnSupport B := by sorry

end WagerFairDiv
