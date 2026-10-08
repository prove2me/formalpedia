-- Prove2me | Theorems.Thm_RoutingBC_Chaining_dependency_chaining
-- name    : RoutingBC.Chaining.dependency_chaining
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:43:53.347136+00:00
-- url     : https://prove2.me/theorems/ba76dd09-0b40-411d-8d4d-1ac5a0dee962
-- title:
--   Lemma 1 (Dependency chaining) — δ̃_{s,t}((s_1,…,s_k)) = δ_{s,t}(s_1)·δ̃_{s_1,t}((s_2,…,s_k))
-- statement:
--   Let $R$ be a loop-free, **source-oblivious** routing scheme on a finite node set $V$ in which every node other than the target forwards with total probability one and the target forwards nothing. Let $s\ne t$ be nodes and $S=(s_1,\dots,s_k)$, $k\ge 1$, an ordered sequence of nodes. Then the probability that a packet sent from $s$ to $t$ passes through all nodes of $S$ in the given order factors as
--   $$\tilde\delta_{s,t}((s_1,\dots,s_k))=\delta_{s,t}(s_1)\cdot\tilde\delta_{s_1,t}((s_2,\dots,s_k)).$$
--   Here $\delta_{s,t}(s_1)$ is the probability that a packet from $s$ to $t$ passes through $s_1$, and $\tilde\delta_{s_1,t}$ is the sequence dependency for packets with source $s_1$.
--
--   The lemma says that once a packet has reached $s_1$, its further path does not depend on where it came from. Iterating it gives the product formula (16) and, after summing over sources, the target dependency chain (17).
--
--   **Formalization Note.** For $k=1$ the right-hand side is $\delta_{s,t}(s_1)\cdot\tilde\delta_{s_1,t}(())$, where the dependency on the empty sequence is the total route probability. No distinctness of the $s_i$ is assumed, as on the page; consecutive repetitions are collapsed by the definition of $\tilde\delta$. The hypothesis that non-target nodes forward with total probability one is implicit in the paper and is needed: if packets could be dropped after $s_1$, the left side would not count them while $\delta_{s,t}(s_1)$ would. Source-obliviousness is the paper's standing assumption of Section 5.
-- source:
--   Dolev, Elovici, Puzis, Routing Betweenness Centrality, BGU CS Tech. Rep. #2009-09 (Aug. 2009), Lemma 1, p. 13 (proof pp. 14–15)

import Mathlib
import Definitions.Def_RoutingBC_Chaining_Routing

namespace RoutingBC.Chaining

theorem dependency_chaining {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V → V → V → ℝ) (hR : IsRoutingScheme R) (hobl : IsSourceOblivious R)
    (s t : V) (hst : s ≠ t) (s₁ : V) (rest : List V) :
    seqDelta R s t (s₁ :: rest) = delta R s t s₁ * seqDelta R s₁ t rest := by sorry

end RoutingBC.Chaining
