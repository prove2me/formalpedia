-- Prove2me | Theorems.Thm_ProjSchedMinCut_Transform_theorem_1
-- name    : ProjSchedMinCut.Transform.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:56.198907+00:00
-- url     : https://prove2.me/theorems/2cdd6ae2-2478-4edd-b68c-6ee7c95019c9
-- title:
--   Theorem 1, p. 7 — (7) is a bijection from finite-capacity n-cuts of D onto feasible solutions of (1)–(5), c(X, X̄) = w(x), and min cut = optimum
-- statement:
--   Consider the project scheduling problem with start-time dependent costs: jobs $J = \{0, \dots, n\}$ with integral processing times $p_j \ge 0$, time lags $(i,j) \in L$ of integral length $d_{ij}$ requiring $S_j \ge S_i + d_{ij}$, a horizon $T$, and costs $w_{jt} \ge 0$ for starting job $j$ at time $t$. Assume that a feasible schedule exists. Let $D = (V, A)$ be the minimum cut digraph of §2.2, built from the earliest and latest feasible start times $e(j)$, $\ell(j)$. Then:
--
--   1. the mapping (7),
--   $$x_{jt} = \begin{cases} 1 & \text{if } (v_{jt}, v_{j,t+1}) \text{ is in the cut } (X, \bar X),\\ 0 & \text{otherwise,}\end{cases}$$
--   is a one-to-one correspondence between the $n$-cuts $(X, \bar X)$ of $D$ with finite capacity and the feasible solutions $x$ of the integer program (1)–(5);
--   2. the capacity $c(X, \bar X)$ of such an $n$-cut equals the value $w(x)$ of the corresponding solution $x$;
--   3. $D$ has a minimum $a$-$b$-cut, and the capacity $c(X, \bar X)$ of every minimum $a$-$b$-cut equals the value $w(x)$ of an optimal solution $x$ of (1)–(5).
--
--   This is the main theoretical result of the paper: the time-indexed formulation of project scheduling with arbitrary time lags and start-time dependent costs is solved by one minimum cut computation, on a digraph with $O(nT)$ nodes and $O(mT)$ arcs. It underlies the Lagrangian lower bounds for resource-constrained project scheduling in §3 of the paper.
--
--   **Formalization Note** The one-to-one correspondence is `Set.BijOn` (maps into, injective on, onto). The standing assumptions of §2 are binders: non-negative weights (p. 5) and the existence of a feasible schedule (p. 4), read within the horizon ($0 \le S_j$, $S_j + p_j \le T$). The paper's jobs $0$ and $n$ are artificial with processing time zero; §2.2 never uses this, so it is not assumed (the statement is stronger). Capacities are in $[0, \infty]$ and compared with $w(x)$ through the embedding of $[0, \infty)$. The existence of a minimum cut is stated explicitly.
-- source:
--   Möhring, Schulz, Stork & Uetz, Solving project scheduling problems by minimum cut computations, manuscript (July 2000, revised April 2002 and November 2002), p. 7, Theorem 1, (7)

import Mathlib
import Definitions.Def_ProjSchedMinCut_Transform_Setting

namespace ProjSchedMinCut.Transform

open Instance

/-- Theorem 1, p. 7: the mapping (7) is a one-to-one correspondence between the `n`-cuts of `D`
of finite capacity and the feasible solutions of (1)–(5); the capacity of such a cut equals the
cost of its image; and the capacity of a minimum `a`-`b`-cut equals the value of an optimal
solution of (1)–(5). -/
theorem theorem_1 {n : ℕ} (I : Instance n) (hw : ∀ j t, 0 ≤ I.w j t)
    (hfeas : ∃ S, I.Feasible S) :
    Set.BijOn I.xOfCut {X | I.IsNCut X ∧ I.cutCap X < ⊤} {x | I.IPFeasible x} ∧
    (∀ X, I.IsNCut X → I.cutCap X < ⊤ →
      I.cutCap X = ENNReal.ofReal (I.cost (I.xOfCut X))) ∧
    ((∃ X, I.IsMinCut X) ∧
      ∀ X, I.IsMinCut X → ∃ x, I.IsOptimal x ∧ I.cutCap X = ENNReal.ofReal (I.cost x)) := by sorry

end ProjSchedMinCut.Transform
