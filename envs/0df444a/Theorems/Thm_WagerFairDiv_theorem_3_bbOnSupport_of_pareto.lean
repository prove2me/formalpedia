-- Prove2me | Theorems.Thm_WagerFairDiv_theorem_3_bbOnSupport_of_pareto
-- name    : WagerFairDiv.theorem_3_bbOnSupport_of_pareto
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:15:57.207997+00:00
-- url     : https://prove2.me/theorems/b79d06b2-6878-4060-aaa6-23840daa212f
-- title:
--   Proof of Theorem 3 (A.3, p.14), "only if", second step (corrected: budget balance only on outcomes some agent reports possible)
-- statement:
--   There are $n$ agents (bettors) and $m$ divisible goods (outcomes). A report profile $\hat{\mathbf v}=(\hat{\mathbf v}_1,\dots,\hat{\mathbf v}_n)$ (written $\hat{\mathbf p}$ on the wagering side) assigns to every agent a point of the probability simplex $\Delta_m=\{x\in\mathbb R^m: x_j\ge0,\ \sum_j x_j=1\}$, and $\mathbf e$ (weights) or $\mathbf w$ (wagers) is a vector of strictly positive reals, with $E=\sum_i e_i$, $W=\sum_i w_i$. For values $x\in\Delta_m$ and a bundle $z\in\mathbb R^m$, $x(z)=\sum_j x_j z_j$. Mechanisms $\mathcal A,\mathcal B$ map $(\hat{\mathbf v},\mathbf e)$ to numbers $\mathcal A_{i,j}(\hat{\mathbf v},\mathbf e)$; $\mathcal A$ and $\mathcal B$ **correspond** (Definition 10) if $\mathcal B_{i,j}(\hat{\mathbf p},\mathbf w)=W\,\mathcal A_{i,j}(\hat{\mathbf p},\mathbf w)$ for all inputs, $i$ and $j$.
--
--   Let $\mathcal A$ be a valid allocation mechanism and $\mathcal B$ its corresponding wagering mechanism. If $\mathcal A$ is Pareto optimal, then for all $\hat{\mathbf p}$, $\mathbf w$ and every outcome $j$ such that $\hat p_{k,j}>0$ for some agent $k$,
--   $$\sum_{i=1}^n\mathcal B_{i,j}(\hat{\mathbf p},\mathbf w)=W.$$
--
--   Unallocated securities of an outcome that some agent reports possible could be given to that agent, a Pareto improvement. The paper concludes strict budget balance on every outcome, which fails for outcomes nobody reports possible.
--
--   Differences from the source:
--   - encoding: agents indexed {1, …, n}, goods / outcomes indexed {1, …, m} → Fin n and Fin m, 0-based; reason: Lean convention; agent 1 of the paper is index 0, no instance changes
--   - reading: reported values v̂ᵢ and reports p̂ᵢ are not given a domain in the text → every report, true value and belief is a point of stdSimplex ℝ (Fin m) (nonnegative, summing to 1); reason: Definition 10 feeds the same (p̂, w) to A and B, true values are normalized (p.2) and beliefs are probabilities (p.3), so reports range over the same type space
--   - encoding: weights eᵢ > 0 and wagers wᵢ > 0 → the subtype PosVec n of strictly positive vectors, E = W = PosVec.total; reason: the same instances as the paper's standing assumptions (pp.2–3)
--   - encoding: A "outputs a feasible allocation" (standing assumption of §2.1, p.2) → explicit hypothesis IsAllocMech A; reason: the paper's definition of an allocation mechanism; the Lean type Mech does not carry it
--   - reading: Pareto optimality over "all alternative allocations" (Definition 3) → alternatives a′ range over feasible allocations (a′ᵢⱼ ≥ 0, Σᵢ a′ᵢⱼ ≤ 1); reason: §2.1, p.2 defines allocations as feasible ones; over infeasible alternatives no mechanism would be Pareto optimal
--   - correction: A Pareto optimal ⇒ B strictly budget balanced (Σᵢ Bᵢⱼ = W for every j) → A Pareto optimal ⇒ Σᵢ Bᵢⱼ(p̂, w) = W for every j with p̂ₖⱼ > 0 for some k (BBOnSupport); reason: the printed step is false: n = 1, m = 2, A₁ⱼ(v̂, e) = 1 if v̂₁ⱼ > 0 else 0 is feasible and Pareto optimal (agent 1 gets value 1, the maximum), yet at v̂₁ = (1, 0) Σᵢ Bᵢ,₂ = 0 < W; the proof's "agent who values it positively" exists exactly when some p̂ₖⱼ > 0
-- source:
--   Freeman, Pennock & Vaughan, An Equivalence Between Wagering and Fair-Division Mechanisms (preprint, 2018), Appendix A.3 (proof of Theorem 3), p.14, "Next, suppose that B is weakly budget balanced but not strictly budget balanced. … We may therefore define a Pareto-improving allocation in which the unallocated portion of good j is allocated to some agent who values it positively". PDF sha256 02e3d24f0ced18523a243feb31fc3e2f28997a9d5a723a0137ed0d2320230580

import Mathlib
import Definitions.Def_WagerFairDiv_Model
import Definitions.Def_WagerFairDiv_AllocationProperties
import Definitions.Def_WagerFairDiv_WageringProperties
import Definitions.Def_WagerFairDiv_CorrespondingMechanisms

namespace WagerFairDiv

/-- Freeman, Pennock & Vaughan, *An Equivalence Between Wagering and Fair-Division Mechanisms*
(preprint, 2018), Appendix A.3 (proof of Theorem 3), p.14, "Next, suppose that B is weakly budget
balanced but not strictly budget balanced", **corrected**: if the (valid) allocation mechanism
`A` is Pareto optimal, the corresponding `B` hands out all `W` securities of every outcome `j`
that some agent reports with positive probability.

**Formalization Note.** The printed step concludes strict budget balance on every outcome; that
is false (n = 1, m = 2: give agent 1 every good she reports positive value for; at
`v̂₁ = (1, 0)` good 2 is wasted, yet the mechanism is Pareto optimal). The proof's
"some agent who values it positively" exists exactly on the outcomes covered here. -/
theorem theorem_3_bbOnSupport_of_pareto {n m : ℕ} (A B : Mech n m) (hA : IsAllocMech A)
    (hAB : Corresponding A B) (hPO : ParetoOptimal A) : BBOnSupport B := by sorry

end WagerFairDiv
