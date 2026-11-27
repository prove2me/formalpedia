-- Prove2me | Theorems.Thm_PathsTreesFlowers_Duality_Supplement_contraction_4_13
-- name    : PathsTreesFlowers.Duality.Supplement.contraction_4_13
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T08:42:58.25482+00:00
-- url     : https://prove2.me/theorems/7c0aa468-0e43-4bab-a7e5-9f4b2a659e46
-- title:
--   4.13 — Shrinking the blossom of a planted flowered tree yields a planted tree, with the blossom vertex outer and precisely the prescribed surviving inner/outer vertices
-- statement:
--   Let $J_F$ be the flowered tree obtained by adding an edge $e$ between outer vertices of a planted tree $J$ for a matching $M$, with root $r$. Let $B$ be its blossom with base $b$. Shrink the vertex set of $B$ using the published block partition. The actual contracted subgraph is a planted tree $K$ for $(G/B,M/B)$ rooted at the image of $r$, with
--   $$E(K)=(E(J)\cup\{e\})/B,$$
--   $$I(K)=q(I(J)\setminus V(B)),\qquad O(K)=\{q(b)\}\cup q(O(J)\setminus V(B)).$$
--
--   Its vertex set is exactly $q(V(J))$, and the blossom vertex $q(b)$ is outer. Every blossom contained in this flowered tree is covered; the theorem does not assume that a separately supplied replacement tree is already planted. Internal edges, including all chords of $B$, disappear in the ambient contraction; surviving parallel edges keep their identities.
--
--   Differences from the source:
--   - encoding: the blossom B in a planted flowered tree J_F → a published blossom whose circuit edges lie in the specified J plus e; reason: J plus e has just one circuit, so this is precisely its blossom and imposes no extra source restriction
--   - encoding: J_F/B and its other inner and outer vertices → a tree with exactly the surviving edge set and image vertex set, inner and outer sets given by the quotient images outside B, and contracted root q(r); reason: the published blockPartition, shrink and shrinkMatching implement 4.9–4.10 without junk vertices
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), p. 458, 4.13

import Mathlib
import Definitions.Def_PathsTreesFlowers_Duality_Supplement_Trees
import Definitions.Def_PathsTreesFlowers_Duality_Shrink

namespace PathsTreesFlowers.Duality.Supplement

open EdmondsMatching65.Polyhedron (IsMatching)

theorem contraction_4_13 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (hM : IsMatching G M) (J : AltTree G) (r : V) (e : E) (u v : V)
    (hF : IsFloweredTree G M J r e u v)
    (bv : List V) (be : List E) (b : V) (hB : IsBlossom G M bv be b)
    (hcontained : be.toFinset ⊆ insert e J.edges) :
    let P := blockPartition bv.toFinset
    ∃ K : AltTree (shrink G P),
      K.edges = shrinkMatching G P (insert e J.edges) ∧
      K.verts = J.verts.image (toPart P) ∧
      K.inner = (J.inner \ bv.toFinset).image (toPart P) ∧
      K.outer = insert (toPart P b) ((J.outer \ bv.toFinset).image (toPart P)) ∧
      toPart P b ∈ K.outer ∧
      IsPlantedTree (shrink G P) (shrinkMatching G P M) K (toPart P r) := by sorry

end PathsTreesFlowers.Duality.Supplement
