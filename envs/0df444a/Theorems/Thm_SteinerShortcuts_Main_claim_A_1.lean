-- Prove2me | Theorems.Thm_SteinerShortcuts_Main_claim_A_1
-- name    : SteinerShortcuts.Main.claim_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:35:47.29336+00:00
-- url     : https://prove2.me/theorems/085b3153-29ee-4351-b4a5-2bb4b3cbd411
-- title:
--   Claim A.1 — the ancestor maximum stays in the replacement interval
-- statement:
--   Use the Appendix A setup: a finite layered DAG, an equal-length critical family satisfying (P1), (P2), an arbitrary Steiner shortcut, one shortest augmented path per critical path, and the retained-edge component $H$. For each vertex $y$ of $H$, form $I_x$, its layer endpoints $\ell_x,r_x$, and the ancestor maximum $\mu_y$ as defined above. Then
--   $$
--   \mu_y\le r_y.
--   $$
--   The maximum includes all ancestors inside $H$, not merely predecessors. Shortest paths, pruning, families and intervals are explicitly constructed from the graph data. The inequality is not an assumption about these objects.
--
--   Differences from the source:
--   - encoding: paths and subpaths as vertex sequences → a starting vertex and a finite tail list; contiguous subpaths and splicing are equalities of vertex lists; reason: this is a nonempty vertex sequence, with validity imposed separately; paths in a layered DAG have no repeated vertices
--   - encoding: a component of Steiner vertices after unused added edges are discarded → a whole weak component with a retained incident edge, including its original endpoints; reason: isolated unused Steiner vertices can be removed; every H vertex then lies on a selected shortest path
--   - encoding: the layer interval endpoints and maximum over H ancestors → finite minimum and maxima, with default zero only on unused empty candidate sets; reason: nonemptiness follows from the source setup and is not added as a hypothesis or built into the data
-- source:
--   Aaron Bernstein, Henry Fleischmann, Bernhard Haeupler, Gary Hoppenworth, Thatchaphol Saranurak, STOC 2027 submission #1034 (October 2026), p. 35, Claim A.1 (PDF p. 37); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1034.pdf

import Mathlib
import Definitions.Def_SteinerShortcuts_Main_Replacement

namespace SteinerShortcuts.Main

theorem claim_A_1 {V W : Type} [Fintype V] [Fintype W]
    (G : Digraph V) (layer : V → ℕ) (hl : IsLayered G layer)
    (paths : Finset (Route V)) (D : ℕ) (hlen : ∀ P ∈ paths, P.length = D)
    (hp1 : P1 G paths) (hp2 : P2 G paths)
    (extra : Finset ((V ⊕ W) × (V ⊕ W))) (he : IsSteinerShortcut G extra)
    (chosen : Route V → Route (V ⊕ W)) (hchosen : ShortestSelection G extra paths chosen)
    (C : Finset W) (hc : ActiveComponent (prunedEdges extra paths chosen) C)
    (y : V ⊕ W) (hy : y ∈ componentVertices (prunedEdges extra paths chosen) C) :
    ancestorMax layer paths chosen (prunedEdges extra paths chosen) C y ≤
      rightLayer layer paths chosen y := by sorry

end SteinerShortcuts.Main
