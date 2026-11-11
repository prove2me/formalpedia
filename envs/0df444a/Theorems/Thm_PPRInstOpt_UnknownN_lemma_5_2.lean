-- Prove2me | Theorems.Thm_PPRInstOpt_UnknownN_lemma_5_2
-- name    : PPRInstOpt.UnknownN.lemma_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:11:41.926735+00:00
-- url     : https://prove2.me/theorems/1ccfe1e8-40e4-4161-8e8f-5be68989953a
-- title:
--   Lemma 5.2 — avoiding an edge set keeps Ω(π(u,v)) of the mass
-- statement:
--   There is a constant $c>0$ depending only on $\alpha$ such that on every valid graph, for every set $E'$ of edges and all vertices $u,v$,
--   $$\max\big\{\pi(u,\overline{E'},v),\ \pi(\mu(E',v),\overline{E'},v)\big\}\ge c\,\pi(u,v),$$
--   where $\mu(E',v)$ maximizes $\pi(w,\overline{E'},v)$ over the heads $w$ of the edges of $E'$ (the second term is absent when $E'=\emptyset$). Equivalently: $\pi(u,\overline{E'},v)\ge c\,\pi(u,v)$, or $\pi(w,\overline{E'},v)\ge c\,\pi(u,v)$ for the head $w$ of some edge of $E'$.
--
--   Differences from the source:
--   - encoding: max{π(u, E̅′, v), π(µ(E′, v), E̅′, v)} = Ω(π(u, v)) with µ an argmax → ∃ c > 0 depending only on α; disjunction over the heads of edges of E′; reason: the max over a finite set is attained, so the forms are equivalent; explicit constant
--   - reading: any set of edges E′ → E′ a finite set of edges of G; reason: edges are edges of the graph
--   - encoding: 'visit an edge' → traverse it (the edge is deleted from P); reason: the paper's walk-path notion
--   - encoding: π(u, v) = probability that the α-discounted walk from u terminates at v → ppr α G u v = Σ_k α(1−α)^k P^k(u, v); reason: the paper's own equivalent form (p. 3); same values
--   - encoding: directed simple graph with every out-degree ≥ 1 and fixed adjacency lists → Digraph V over an arbitrary vertex type: duplicate-free out- and in-lists describing one edge set, no self-loops, nonempty out-lists; reason: same instances; list order fixes out(v, i) and in(v, i)
-- source:
--   Bertram, Jensen, Thorup, Wang, Yan, Instance-Optimality of Single-Pair Personalized PageRank, STOC 2027 submission (manuscript sha256 e1dc6b7d…), p. 32, Lemma 5.2, Eq. (33)

import Mathlib
import Definitions.Def_PPRInstOpt_UnknownN_Graph

namespace PPRInstOpt.UnknownN

/-- Lemma 5.2 (p. 32): there is a constant `c > 0` depending only on `α` such that for any vertices
`u, v` and any set `E'` of edges, `max{π(u, \bar{E'}, v), π(µ(E', v), \bar{E'}, v)} ≥ c π(u, v)`,
where `µ(E', v)` maximizes `π(w, \bar{E'}, v)` over the heads `w` of the edges of `E'`; that is,
`π(u, \bar{E'}, v) ≥ c π(u, v)` or `π(w, \bar{E'}, v) ≥ c π(u, v)` for the head `w` of some edge
of `E'`. -/
theorem lemma_5_2 (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : Digraph V) (E' : Finset (V × V)),
        (∀ e ∈ E', e.2 ∈ G.outList e.1) → ∀ u v : V,
          c * ppr α G u v ≤ pprAvoid α G E' u v ∨
            ∃ e ∈ E', c * ppr α G u v ≤ pprAvoid α G E' e.2 v := by sorry

end PPRInstOpt.UnknownN
