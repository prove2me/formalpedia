-- Prove2me | Theorems.Thm_RoutingBC_Chaining_sequence_dependency_product
-- name    : RoutingBC.Chaining.sequence_dependency_product
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:42:42.269253+00:00
-- url     : https://prove2.me/theorems/1869581c-6c3c-49f9-8895-9ca428d9471d
-- title:
--   Eq. (16) — δ̃_{s,t}((s_1,…,s_k)) = δ_{s,t}(s_1)·δ_{s_1,t}(s_2)⋯δ_{s_{k−1},t}(s_k)
-- statement:
--   Under the hypotheses of Lemma 1 (a loop-free, source-oblivious routing scheme on a finite node set, total forwarding probability one at every non-target node, a silent target), let $s\ne t$ and let $S=(s_1,\dots,s_k)$ with $k\ge1$. Then the sequence dependency is a product of pairwise dependencies on single nodes:
--   $$\tilde\delta_{s,t}((s_1,\dots,s_k))=\delta_{s,t}(s_1)\cdot\prod_{i=2}^{k}\delta_{s_{i-1},t}(s_i).$$
--
--   This is what lets the RBC of a sequence be evaluated from precomputed pairwise dependencies of single nodes.
--
--   **Formalization Note.** The page prints the second factor as $\delta_{s_1,t}(s_1)$; the intended factor is $\delta_{s_1,t}(s_2)$, as the Figure 4 caption ($\tilde\delta_{s,t}((u,v))=\delta_{s,t}(u)\cdot\delta_{u,t}(v)=\tfrac13\cdot\tfrac12$) and Lemma 1 confirm, and the corrected product is stated. The product runs over the consecutive pairs $(s_{i-1},s_i)$ of $S$ (empty for $k=1$). No distinctness of the $s_i$ is assumed.
-- source:
--   Dolev, Elovici, Puzis, Routing Betweenness Centrality, BGU CS Tech. Rep. #2009-09 (Aug. 2009), Section 5.2, Eq. (16), p. 15

import Mathlib
import Definitions.Def_RoutingBC_Chaining_Routing

namespace RoutingBC.Chaining

theorem sequence_dependency_product {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V → V → V → ℝ) (hR : IsRoutingScheme R) (hobl : IsSourceOblivious R)
    (s t : V) (hst : s ≠ t) (s₁ : V) (rest : List V) :
    seqDelta R s t (s₁ :: rest) =
      delta R s t s₁ * (((s₁ :: rest).zip rest).map (fun ab => delta R ab.1 t ab.2)).prod := by sorry

end RoutingBC.Chaining
