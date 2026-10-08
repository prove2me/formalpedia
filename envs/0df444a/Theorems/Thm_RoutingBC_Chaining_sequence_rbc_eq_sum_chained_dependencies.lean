-- Prove2me | Theorems.Thm_RoutingBC_Chaining_sequence_rbc_eq_sum_chained_dependencies
-- name    : RoutingBC.Chaining.sequence_rbc_eq_sum_chained_dependencies
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:42:41.662725+00:00
-- url     : https://prove2.me/theorems/3289d5ad-3502-4ba6-9e30-65445c0b3057
-- title:
--   Sequence RBC = Σ_t δ_{•,t}(s_1)ρ_{s_1}·∏ δ_{s_i,t}(s_{i+1})ρ_{s_{i+1}} (Section 5.2, Algorithm 6)
-- statement:
--   Let $R$ be a loop-free, source-oblivious routing scheme on a finite node set $V$ in which every node other than the target forwards with total probability one and the target forwards nothing. Let $T:V\times V\to\mathbb R$ be a traffic matrix, $\rho:V\to[0,1]$ sampling rates, and $S=(s_1,\dots,s_k)$, $k\ge1$, a sequence of **distinct** nodes. Then the routing betweenness centrality of the sequence,
--   $$\tilde\delta_{\bullet,\bullet}(S_\rho)=\prod_{r\in S}\rho_r\cdot\sum_{s,t\in V}\tilde\delta_{s,t}(S)\,T(s,t),$$
--   equals
--   $$\sum_{t\in V}\delta_{\bullet,t}(s_1)\,\rho_{s_1}\cdot\prod_{i=1}^{k-1}\delta_{s_i,t}(s_{i+1})\,\rho_{s_{i+1}},$$
--   where $\delta_{\bullet,t}(v)=\sum_{s\in V}\delta_{s,t}(v)\,T(s,t)$ is the target dependency and $\delta_{s_i,t}(s_{i+1})$ the pairwise dependency.
--
--   The left side is the expected number of packets sampled by all monitors of $S$ in order (Eq. (4)); the right side is the value returned by Algorithm 6, which needs only the precomputed target dependencies of $s_1$ and pairwise dependencies between consecutive members of $S$. The sum on the left runs over all pairs $(s,t)$, endpoints included.
--
--   **Formalization Note.** Algorithm 6 indexes the sequence from $0$ ($S=\{s_0,\dots,s_k\}$); here it is $(s_1,\dots,s_k)$ as in Lemma 1, and the product runs over the consecutive pairs of $S$. Distinctness of $S$ is the paper's assumption for Eq. (4). The running time $O(n\cdot|S|)$ is not formalized; only the identity is. No sign condition on $T$ is assumed; the bounds $0\le\rho_v\le1$ are the page's.
-- source:
--   Dolev, Elovici, Puzis, Routing Betweenness Centrality, BGU CS Tech. Rep. #2009-09 (Aug. 2009), Section 5.2, Eqs. (11), (17) and the display after (17), pp. 13–15; Algorithm 6, p. 16; Eq. (4), p. 8

import Mathlib
import Definitions.Def_RoutingBC_Chaining_Routing

namespace RoutingBC.Chaining

theorem sequence_rbc_eq_sum_chained_dependencies {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V → V → V → ℝ) (hR : IsRoutingScheme R) (hobl : IsSourceOblivious R)
    (T : V → V → ℝ) (ρ : V → ℝ) (hρ : ∀ v, 0 ≤ ρ v ∧ ρ v ≤ 1)
    (s₁ : V) (rest : List V) (hS : (s₁ :: rest).Nodup) :
    seqRBC R T ρ (s₁ :: rest) =
      ∑ t, targetDelta R T t s₁ * ρ s₁ *
        (((s₁ :: rest).zip rest).map (fun ab => delta R ab.1 t ab.2 * ρ ab.2)).prod := by sorry

end RoutingBC.Chaining
