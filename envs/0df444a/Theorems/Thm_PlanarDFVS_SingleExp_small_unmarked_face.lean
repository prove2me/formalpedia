-- Prove2me | Theorems.Thm_PlanarDFVS_SingleExp_small_unmarked_face
-- name    : PlanarDFVS.SingleExp.small_unmarked_face
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:48.083177+00:00
-- url     : https://prove2.me/theorems/9854571f-223d-40fb-996e-92e752f9cc0e
-- title:
--   Lemma 5.1 — an unmarked face with at most four candidates
-- statement:
--   Let $D$ be a strongly connected loopless plane digraph with at least one arc. Let $M$ be a set of circular faces and let $U$ contain every vertex incident to any face of $M$. Put $P=\{v\notin U:b(v)>1\}$. If $|P|\ge3|M|$, then
--
--   $$\exists f\text{ circular},\quad f\notin M,\quad |V(f)\cap P|\le4.$$
--
--   Vertex-face incidences in this bound count distinct vertices, whereas the definitions of $a$ and $b$ retain corner multiplicity. The all-boundary-vertices-in-$U$ premise is retained exactly; it is not silently assumed to hold in the deterministic recursion.
--
--   Differences from the source:
--   - encoding: finite vertex and arc sets with corner incidences → Fin n vertices, Fin m arc identities and paired incidence darts; closed walks define cycles; reason: finite relabeling retains loops, parallel arcs and repeated facial incidences; a nonempty closed directed walk contains a directed cycle
--   - encoding: crossing-free plane embedding and its cyclic incidence orders → continuous crossing-free curves with locally straight endpoint germs and ray-ordered rotations; reason: local straightening realizes every finite topological embedding with the same rotations and facial walks; no Euler or target inequality is assumed
--   - reading: strongly connected plane digraph, using the nontrivial cyclic-component setting and Lemma 3.2 → looplessness and at least one arc are explicit alongside strong connectivity; reason: inherited preprocessing context excludes the edgeless singleton, for which the invoked b(v)≥1 assertion and facial conclusion have no intended cyclic interpretation
-- source:
--   Daniel Lokshtanov, Saket Saurabh, Jie Xue, STOC 2027 submission #1569 (October 2026), p. 12 (PDF p. 12), Lemma 5.1

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Interfaces

open scoped BigOperators
open Classical

namespace PlanarDFVS.SingleExp

theorem small_unmarked_face (n m : ℕ) (G : Graph n m) (E : Drawing G)
    (hc : StronglyConnected G) (hm : 0 < m) (hl : Loopless G)
    (M : Finset (Finset (Dart m))) (hM : M ⊆ circularFaces E)
    (U : Finset (Fin n))
    (hU : ∀ f ∈ M, incidentVertices (G := G) f ⊆ U)
    (hp : 3 * M.card ≤ ((positive E) \ U).card) :
    ∃ f ∈ circularFaces E, f ∉ M ∧
      ((incidentVertices (G := G) f) ∩ ((positive E) \ U)).card ≤ 4 := by sorry

end PlanarDFVS.SingleExp
