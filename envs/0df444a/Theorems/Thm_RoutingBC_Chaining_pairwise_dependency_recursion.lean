-- Prove2me | Theorems.Thm_RoutingBC_Chaining_pairwise_dependency_recursion
-- name    : RoutingBC.Chaining.pairwise_dependency_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:42:51.056553+00:00
-- url     : https://prove2.me/theorems/6adf93d4-a212-4ad8-b751-94a1c433fcce
-- title:
--   Eq. (1) — δ_{s,t}(s) = 1 and δ_{s,t}(v) = Σ_{u∈Pred_{s,t}(v)} δ_{s,t}(u)·R(s,u,v,t)
-- statement:
--   Let $R$ be a loop-free routing scheme on a finite node set $V$ (nonnegative, total forwarding probability one at every non-target node, silent target); the decisions may depend on the source. Fix $s,t\in V$ and let $\mathrm{Pred}_{s,t}(v)=\{u : R(s,u,v,t)>0\}$ be the set of immediate predecessors of $v$ on the way to $t$. Then
--   $$\delta_{s,t}(s)=1,\qquad \delta_{s,t}(v)=\sum_{u\in \mathrm{Pred}_{s,t}(v)}\delta_{s,t}(u)\cdot R(s,u,v,t)\quad (v\ne s).$$
--
--   This recursion computes all pairwise dependencies of a pair $(s,t)$ by one pass over a topological order of the routing DAG, which is Algorithm 1 of the paper.
--
--   **Formalization Note.** The page writes the second line of (1) without "$v\ne s$"; at $v=s$ the first line applies instead (the right side of the second line is $0$ there, by loop-freeness). Both lines are stated without source-obliviousness.
-- source:
--   Dolev, Elovici, Puzis, Routing Betweenness Centrality, BGU CS Tech. Rep. #2009-09 (Aug. 2009), Section 4.1, Eq. (1), p. 6

import Mathlib
import Definitions.Def_RoutingBC_Chaining_Routing

namespace RoutingBC.Chaining

theorem pairwise_dependency_recursion {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V → V → V → ℝ) (hR : IsRoutingScheme R) (s t : V) :
    delta R s t s = 1 ∧
      ∀ v, v ≠ s →
        delta R s t v =
          ∑ u ∈ Finset.univ.filter (fun u => 0 < R s u v t), delta R s t u * R s u v t := by sorry

end RoutingBC.Chaining
