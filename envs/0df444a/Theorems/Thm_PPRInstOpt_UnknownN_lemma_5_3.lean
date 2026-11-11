-- Prove2me | Theorems.Thm_PPRInstOpt_UnknownN_lemma_5_3
-- name    : PPRInstOpt.UnknownN.lemma_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:11:58.606472+00:00
-- url     : https://prove2.me/theorems/46da551d-9b9a-48f4-8f35-7bf513591c46
-- title:
--   Lemma 5.3 ([TW26] Lemma 3.2) — subdividing an edge lowers π by a factor at most (2 − α)/(1 − α)
-- statement:
--   Let $(u,v)$ be an edge of a valid graph $G$ and let $G'$ be obtained by replacing it with edges $(u,w)$ and $(w,v)$ for a new vertex $w$ (the edge $(u,w)$ takes the place of $(u,v)$ in $u$'s list). Then for all vertices $u',v'$ of $G$
--   $$\frac{1-\alpha}{2-\alpha}\,\pi_G(u',v')\le\pi_{G'}(u',v')\le\pi_G(u',v').$$
--
--   Differences from the source:
--   - reading: π(u′, v′) can only be decreased by a factor of at most (2 − α)/(1 − α) → both π_{G′} ≤ π_G and π_{G′} ≥ ((1 − α)/(2 − α)) π_G; reason: the two halves of the sentence
--   - encoding: w a new vertex → G′ a Digraph on Option V with w = none and out-lists subdivOut G u v; reason: same graph; in-lists are determined up to order, which π does not see
--   - encoding: π(u, v) = probability that the α-discounted walk from u terminates at v → ppr α G u v = Σ_k α(1−α)^k P^k(u, v); reason: the paper's own equivalent form (p. 3); same values
--   - encoding: directed simple graph with every out-degree ≥ 1 and fixed adjacency lists → Digraph V over an arbitrary vertex type: duplicate-free out- and in-lists describing one edge set, no self-loops, nonempty out-lists; reason: same instances; list order fixes out(v, i) and in(v, i)
-- source:
--   Bertram, Jensen, Thorup, Wang, Yan, Instance-Optimality of Single-Pair Personalized PageRank, STOC 2027 submission (manuscript sha256 e1dc6b7d…), p. 33, Lemma 5.3

import Mathlib
import Definitions.Def_PPRInstOpt_UnknownN_Graph

namespace PPRInstOpt.UnknownN

/-- Lemma 5.3 ([TW26] Lemma 3.2, p. 33): replace an edge `(u, v)` by edges `(u, w)`, `(w, v)` with a
new vertex `w` (`G'` on `Option V`, `w = none`). Then for all old vertices `u', v'`,
`π_{G'}(u', v')` is at most `π_G(u', v')` and at least `((1 - α)/(2 - α)) π_G(u', v')`. -/
theorem lemma_5_3 {V : Type} [Fintype V] [DecidableEq V] (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (G : Digraph V) (u v : V) (huv : v ∈ G.outList u) (G' : Digraph (Option V))
    (hG' : ∀ x, G'.outList x = subdivOut G u v x) (u' v' : V) :
    ppr α G' (some u') (some v') ≤ ppr α G u' v' ∧
      (1 - α) / (2 - α) * ppr α G u' v' ≤ ppr α G' (some u') (some v') := by sorry

end PPRInstOpt.UnknownN
