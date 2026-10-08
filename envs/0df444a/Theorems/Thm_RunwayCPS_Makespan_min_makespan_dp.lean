-- Prove2me | Theorems.Thm_RunwayCPS_Makespan_min_makespan_dp
-- name    : RunwayCPS.Makespan.min_makespan_dp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:12:20.815987+00:00
-- url     : https://prove2.me/theorems/81b79bcc-330b-41c5-896e-696ada879884
-- title:
--   §4.1 — the DP on the pruned CPS network decides feasibility and gives the minimum makespan
-- statement:
--   Consider a runway instance with $n\ge1$ aircraft, maximum shift $k$, nonnegative separations satisfying the triangle inequality $\delta_{ac}\le\delta_{ab}+\delta_{bc}$, time windows $[e(a),l(a)]$, and precedence pairs of distinct aircraft. A feasible schedule is a $k$-CPS sequence with landing times satisfying the windows, all pairwise separations, and the precedence pairs; its makespan is the landing time of the last aircraft. Let $G$ be the precedence-pruned CPS network and $T^*$ the dynamic program (1) on it, with $T^*(\cdot)=e(\cdot)$ at stage 1. Then:
--
--   1. a feasible schedule exists if and only if
--   $$\exists\, j \text{ in stage } n \text{ of } G:\quad T^*(j)\le l(j);$$
--   2. for every real $\tau$, $\tau$ is the minimum makespan over feasible schedules if and only if
--   $$\tau=\min\{\,T^*(j)\ :\ j \text{ in stage } n \text{ of } G,\ T^*(j)\le l(j)\,\}.$$
--
--   This is the algorithm of §4.1 and Figure 2: one left-to-right pass of the recursion over a network with polynomially many nodes for fixed $k$ solves the minimum makespan problem with time windows and precedence constraints.
--
--   **Formalization Note** The paper takes "the lowest value of $T^*(\cdot)$ among all nodes in stage $n$"; that value can come from a node whose final aircraft lands after its latest time, so the minimum is taken here over the stage-$n$ nodes with $T^*(j)\le l(j)$, which is also the paper's feasibility check. Part 2 is stated with `IsLeast` on both sides, so the minimum makespan is attained exactly when the right-hand minimum exists; part 1 pins down feasibility. Running times (Proposition 1) and the reconstruction of the optimal sequence through predecessor pointers are not formalized.
-- source:
--   Balakrishnan & Chandran, Algorithms for Scheduling Runway Operations Under Constrained Position Shifting, Oper. Res. 58(6) (2010), p. 1655, §4.1, minimum makespan rule and feasibility check (with Figure 2), resting on Lemma 3 and Theorem 1

import Mathlib
import Definitions.Def_RunwayCPS_Makespan_DP

namespace RunwayCPS.Makespan

/-- §4.1 (p. 1655), minimum makespan rule with the feasibility check, resting on Lemma 3 and
Theorem 1: under nonnegative separations satisfying the triangle inequality and precedence
pairs of distinct aircraft,
1. a feasible schedule exists if and only if some stage-`n` node `j` of the pruned network has
   `T*(j) ≤ l(j)`;
2. a real `τ` is the minimum makespan over feasible schedules if and only if it is the least
   value `T*(j)` over the stage-`n` nodes `j` of the pruned network with `T*(j) ≤ l(j)`. -/
theorem min_makespan_dp {n : ℕ} [NeZero n] (I : Instance n)
    (hδ : ∀ a b, 0 ≤ I.δ a b) (htri : ∀ a b c, I.δ a c ≤ I.δ a b + I.δ b c)
    (hprec : ∀ xy ∈ I.prec, xy.1 ≠ xy.2) :
    ((∃ σ t, IsFeasible I σ t) ↔
        ∃ j ∈ GNodes I n, T I n j ≤ ((I.l (final j) : ℝ) : WithTop ℝ)) ∧
    ∀ τ : ℝ,
      IsLeast {m : ℝ | ∃ σ t, IsFeasible I σ t ∧ m = makespan t} τ ↔
        IsLeast {m : ℝ | ∃ j ∈ GNodes I n, T I n j = (m : WithTop ℝ) ∧ m ≤ I.l (final j)} τ := by sorry

end RunwayCPS.Makespan
