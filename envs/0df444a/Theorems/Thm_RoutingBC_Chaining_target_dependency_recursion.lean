-- Prove2me | Theorems.Thm_RoutingBC_Chaining_target_dependency_recursion
-- name    : RoutingBC.Chaining.target_dependency_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:42:53.391027+00:00
-- url     : https://prove2.me/theorems/1ba0fcd9-b2e5-4afc-a28a-bc46990639c0
-- title:
--   Eq. (9) — δ_{•,t}(v) = T(v,t) + Σ_{u∈Pred_t(v)} δ_{•,t}(u)·R(∅,u,v,t)
-- statement:
--   Let $R$ be a loop-free, source-oblivious routing scheme on a finite node set $V$ (total forwarding probability one at every non-target node, silent target), and $T:V\times V\to\mathbb R$ a traffic matrix. Since the scheme does not depend on the source, write $R(\oslash,u,v,t)$ for the common value of $R(s,u,v,t)$, and $\mathrm{Pred}_t(v)=\{u : R(\oslash,u,v,t)>0\}$. Then for every target $t$ and node $v$,
--   $$\delta_{\bullet,t}(v)=T(v,t)+\sum_{u\in\mathrm{Pred}_t(v)}\delta_{\bullet,t}(u)\cdot R(\oslash,u,v,t).$$
--
--   The expected number of packets targeted at $t$ that pass through $v$ consists of those injected at $v$ and those forwarded to $v$ by its predecessors; this recursion is Algorithm 4 of the paper, which replaces the loop over source–target pairs by a loop over targets.
--
--   **Formalization Note.** The "don't care" source $\oslash$ is represented by an arbitrary fixed node $s_0$; by source-obliviousness the value does not depend on the choice. No sign condition on $T$ is assumed.
-- source:
--   Dolev, Elovici, Puzis, Routing Betweenness Centrality, BGU CS Tech. Rep. #2009-09 (Aug. 2009), Section 5.1, Eq. (9), p. 11

import Mathlib
import Definitions.Def_RoutingBC_Chaining_Routing

namespace RoutingBC.Chaining

theorem target_dependency_recursion {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V → V → V → ℝ) (hR : IsRoutingScheme R) (hobl : IsSourceOblivious R)
    (T : V → V → ℝ) (s₀ t v : V) :
    targetDelta R T t v =
      T v t + ∑ u ∈ Finset.univ.filter (fun u => 0 < R s₀ u v t),
        targetDelta R T t u * R s₀ u v t := by sorry

end RoutingBC.Chaining
