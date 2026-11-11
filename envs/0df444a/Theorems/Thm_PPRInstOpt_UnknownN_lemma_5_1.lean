-- Prove2me | Theorems.Thm_PPRInstOpt_UnknownN_lemma_5_1
-- name    : PPRInstOpt.UnknownN.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:11:40.151194+00:00
-- url     : https://prove2.me/theorems/29cb6e56-c6e4-4038-9223-9fbde604f694
-- title:
--   Lemma 5.1 — π(u,v) ≥ π(u,w) π(w,v)
-- statement:
--   On every valid graph, for any vertices $u,v,w$,
--   $$\pi(u,v)\ge\pi(u,w)\,\pi(w,v).$$
--
--   Differences from the source:
--   - encoding: π(u, v) = probability that the α-discounted walk from u terminates at v → ppr α G u v = Σ_k α(1−α)^k P^k(u, v); reason: the paper's own equivalent form (p. 3); same values
--   - encoding: directed simple graph with every out-degree ≥ 1 and fixed adjacency lists → Digraph V over an arbitrary vertex type: duplicate-free out- and in-lists describing one edge set, no self-loops, nonempty out-lists; reason: same instances; list order fixes out(v, i) and in(v, i)
-- source:
--   Bertram, Jensen, Thorup, Wang, Yan, Instance-Optimality of Single-Pair Personalized PageRank, STOC 2027 submission (manuscript sha256 e1dc6b7d…), p. 32, Lemma 5.1

import Mathlib
import Definitions.Def_PPRInstOpt_UnknownN_Graph

namespace PPRInstOpt.UnknownN

/-- Lemma 5.1 (p. 32): for any vertices `u, v, w`, `π(u, v) ≥ π(u, w) π(w, v)`. -/
theorem lemma_5_1 {V : Type} [Fintype V] [DecidableEq V] (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (G : Digraph V) (u v w : V) :
    ppr α G u w * ppr α G w v ≤ ppr α G u v := by sorry

end PPRInstOpt.UnknownN
