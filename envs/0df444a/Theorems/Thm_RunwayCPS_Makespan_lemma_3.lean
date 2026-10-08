-- Prove2me | Theorems.Thm_RunwayCPS_Makespan_lemma_3
-- name    : RunwayCPS.Makespan.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:12:03.17361+00:00
-- url     : https://prove2.me/theorems/b9119bf9-f435-408c-be45-b9d250b57f9e
-- title:
--   Lemma 3 — the recursion (1) computes the earliest landing time $T^*(j)$
-- statement:
--   Consider a runway instance whose separations are nonnegative and satisfy the triangle inequality
--
--   $$\delta_{ac}\le\delta_{ab}+\delta_{bc}\quad\text{for all aircraft } a,b,c,$$
--
--   and let $G$ be the precedence-pruned CPS network. For a stage-$p$ node $j$ of $G$, let $\mathrm{arr}(p,j)$ be the set of landing times of the final aircraft of $j$ over all partial schedules ending at $j$: paths $v_1,\dots,v_p=j$ in $G$ with times respecting the windows of $v_1,\dots,v_{p-1}$, the earliest time of $j$, and the pairwise separations. Let $T^*(j)$ be given by the recursion (1),
--
--   $$T^*(j)=\max\Big\{e(j),\ \min_{i\in P(j):\,T^*(i)\le l(i)}\big(T^*(i)+\delta_i(j)\big)\Big\},\qquad T^*(j)=e(j)\text{ at stage }1.$$
--
--   Then for every stage $1\le p\le n$ and every stage-$p$ node $j$ of $G$:
--
--   1. for every real $\tau$, $T^*(j)=\tau$ if and only if $\tau$ is the least element of $\mathrm{arr}(p,j)$;
--   2. $T^*(j)=+\infty$ if and only if $\mathrm{arr}(p,j)$ is empty.
--
--   So the recursion computes the earliest feasible arrival time of the final aircraft of every node, and detects nodes that no feasible partial schedule reaches.
--
--   **Formalization Note** $T^*$ is the recursion with values in `WithTop ℝ`; the earliest arrival time is defined independently through partial schedules, which impose all pairwise separations (the recursion adds only consecutive ones, which is where the triangle inequality enters).
-- source:
--   Balakrishnan & Chandran, Algorithms for Scheduling Runway Operations Under Constrained Position Shifting, Oper. Res. 58(6) (2010), pp. 1654–1655, Lemma 3, Eq. (1), Table 2; boundary condition from §4.1

import Mathlib
import Definitions.Def_RunwayCPS_Makespan_DP

namespace RunwayCPS.Makespan

/-- Lemma 3 (pp. 1654–1655): under nonnegative separations satisfying the triangle inequality,
the dynamic programming recursion (1) computes `T*(j)`, the earliest landing time of the final
aircraft of `j` over all partial schedules ending at `j`: for every stage `p` and every
stage-`p` node `j` of the pruned network, `T p j` is the least element of `arrivals p j` when
that set is nonempty, and `T p j = +∞` exactly when it is empty. -/
theorem lemma_3 {n : ℕ} [NeZero n] (I : Instance n)
    (hδ : ∀ a b, 0 ≤ I.δ a b) (htri : ∀ a b c, I.δ a c ≤ I.δ a b + I.δ b c)
    (p : ℕ) (hp1 : 1 ≤ p) (hpn : p ≤ n) (j : List (Fin n)) (hj : IsGNode I p j) :
    (∀ τ : ℝ, T I p j = (τ : WithTop ℝ) ↔ IsLeast (arrivals I p j) τ) ∧
    (T I p j = ⊤ ↔ arrivals I p j = ∅) := by sorry

end RunwayCPS.Makespan
