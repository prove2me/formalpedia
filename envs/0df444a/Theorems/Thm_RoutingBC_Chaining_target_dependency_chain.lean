-- Prove2me | Theorems.Thm_RoutingBC_Chaining_target_dependency_chain
-- name    : RoutingBC.Chaining.target_dependency_chain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:42:37.954379+00:00
-- url     : https://prove2.me/theorems/61e404f0-7936-4b5d-a2b5-3895fcf59093
-- title:
--   Eq. (17) — target dependency chain δ̃_{•,t}((s_1,…,s_k)) = δ_{•,t}(s_1)·∏_{i=2}^{k} δ_{s_{i−1},t}(s_i)
-- statement:
--   Let $R$ be a loop-free, source-oblivious routing scheme on a finite node set $V$ (total forwarding probability one at every non-target node, silent target), $T:V\times V\to\mathbb R$ a traffic matrix, $t\in V$ a target and $S=(s_1,\dots,s_k)$ with $k\ge1$. Write $\delta_{\bullet,t}(v)=\sum_{s\in V}\delta_{s,t}(v)\,T(s,t)$ and $\tilde\delta_{\bullet,t}(S)=\sum_{s\in V}\tilde\delta_{s,t}(S)\,T(s,t)$ for the target dependencies. Then
--   $$\tilde\delta_{\bullet,t}((s_1,\dots,s_k))=\delta_{\bullet,t}(s_1)\cdot\prod_{i=2}^{k}\delta_{s_{i-1},t}(s_i).$$
--
--   The expected number of packets targeted at $t$ that pass through the whole sequence is thus the target dependency of its first node times a chain of pairwise dependencies, which no longer involves the sources.
--
--   **Formalization Note.** The page prints the product as $\prod_{i=1}^{k}\delta_{v_{i-1},t}(s_i)$; $v$ is a misprint for $s$, and the index $i=1$ would refer to a nonexistent $s_0$, so the product over $i=2,\dots,k$ (the consecutive pairs of $S$) is stated. The sum over sources includes $s=t$, which Lemma 1 excludes; the identity is claimed for every source, with no assumption on $T(t,t)$. No sign condition on $T$ is assumed.
-- source:
--   Dolev, Elovici, Puzis, Routing Betweenness Centrality, BGU CS Tech. Rep. #2009-09 (Aug. 2009), Section 5.2, Eq. (17), p. 15

import Mathlib
import Definitions.Def_RoutingBC_Chaining_Routing

namespace RoutingBC.Chaining

theorem target_dependency_chain {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V → V → V → ℝ) (hR : IsRoutingScheme R) (hobl : IsSourceOblivious R)
    (T : V → V → ℝ) (t s₁ : V) (rest : List V) :
    targetSeqDelta R T t (s₁ :: rest) =
      targetDelta R T t s₁ *
        (((s₁ :: rest).zip rest).map (fun ab => delta R ab.1 t ab.2)).prod := by sorry

end RoutingBC.Chaining
