-- Prove2me | Theorems.Thm_WeakGraphOracles_OneSided_Supplement_lemma_7_3
-- name    : WeakGraphOracles.OneSided.Supplement.lemma_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:27:33.493099+00:00
-- url     : https://prove2.me/theorems/0289566a-fc2d-43ec-b4c1-948283857fb6
-- title:
--   Lemma 7.3 — induced embeddings against their maximum pair load give $|E(G)\oplus E(G')|\ge|C|/c_{\max}$
-- statement:
--   Let $H$ be a graph with at least two vertices and $G$ a graph on $n$ labels. An induced embedding of $H$ into $G$ is an injective map $\phi:V(H)\to V(G)$ with $(\phi(a),\phi(b))\in E(G)$ exactly when $(a,b)\in E(H)$. Let $C$ be a nonempty set of induced embeddings of $H$ into $G$. For vertices $x\ne y$ of $G$ let $c(x,y)$ be the number of $\phi\in C$ with $x,y\in\phi(V(H))$, and let $c_{\max}=\max_{x\ne y}c(x,y)$. Then every graph $G'$ on the labels of $G$ that has no induced copy of $H$ satisfies
--
--   $$|E(G)\oplus E(G')|\ \ge\ \frac{|C|}{c_{\max}},$$
--
--   where $E(G)\oplus E(G')$ counts the vertex pairs, edges and non-edges alike, on which $G$ and $G'$ differ.
--
--   This counting lemma converts many induced copies with small pair overlap into a lower bound on the edit distance to induced $H$-freeness, and is the source of the farness bounds of Lemma 7.4.
--
--   Differences from the source:
--   - generalization: H the fixed pattern of Section 7.6 (connected, no isolated vertex, so at least two vertices) → any pattern H with at least two vertices; reason: the proof uses no other property of H; the source's H has at least two vertices, so the statement specializes
-- source:
--   Oded Lachish, Amit Levi, Ilan Newman, Testability of General Graphs with Weak Query Oracles, STOC 2027 submission #274 (October 2026), p. 19 (PDF p. 20), Lemma 7.3 (with the definition of induced embedding on the same page); proof p. 19 (PDF p. 20)

import Mathlib
import Definitions.Def_WeakGraphOracles_OneSided_Supplement_models
import Definitions.Def_WeakGraphOracles_OneSided_Supplement_constructions

set_option autoImplicit false

namespace WeakGraphOracles.OneSided.Supplement

/-- Lemma 7.3, printed p. 19 (PDF p. 20). `H` has at least two vertices; `C` is a
nonempty set of induced embeddings of `H` into `G`; `c(x,y)` counts the members
whose image contains `x` and `y`, and `c_max = max_{x ≠ y} c(x,y)`. Every
induced-`H`-free graph `G'` on the labels of `G` differs from `G` on at least
`|C| / c_max` vertex pairs (edges and non-edges). -/
theorem lemma_7_3 (H : Pattern) (hH : 2 ≤ H.order) {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Finset (H.graph ↪g G)) (hC : C.Nonempty) (G' : SimpleGraph (Fin n))
    (hG' : InducedFree {H} G') :
    (C.card : ℝ) / (maxPairLoad C : ℝ) ≤ (symmDiffCard G G' : ℝ) := by sorry

end WeakGraphOracles.OneSided.Supplement
