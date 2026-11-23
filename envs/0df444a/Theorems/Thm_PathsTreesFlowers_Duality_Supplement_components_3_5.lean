-- Prove2me | Theorems.Thm_PathsTreesFlowers_Duality_Supplement_components_3_5
-- name    : PathsTreesFlowers.Duality.Supplement.components_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:36:59.534097+00:00
-- url     : https://prove2.me/theorems/17f63deb-aa21-4a64-a4d0-1e62c0548939
-- title:
--   3.5 — Every component of the symmetric difference of two matchings is a path or circuit alternating for both, with each path endpoint exposed for one matching
-- statement:
--   Let $M_1$ and $M_2$ be matchings in a finite loopless multigraph $G$. For every connected component $C$ of the graph formed by their symmetric difference,
--   $$F=(M_1\setminus M_2)\cup(M_2\setminus M_1),$$
--   $C$ is a path or a circuit alternating for both matchings. Every endpoint in the path case is exposed for at least one of $M_1,M_2$.
--
--   The same vertex and edge lists describe the whole component in both alternation assertions. This is the decomposition used to compare matchings; it includes two-edge circuits of parallel edges and has no components when $F$ is empty.
--
--   Differences from the source:
--   - encoding: the components of the graph formed by M₁ + M₂ → connected nonempty subgraphs closed under incident symmetric-difference edges, with exactly the internal edges; reason: 3.0 and 3.1 specify components and an edge-formed graph with exactly its endpoints
--   - encoding: paths and circuits as subgraphs → vertex and edge lists with exact component sets and cyclic circuit alternation; reason: orientation and cyclic starting position only choose representatives of the same source subgraphs
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), p. 453, 3.5

import Mathlib
import Definitions.Def_PathsTreesFlowers_Duality_Supplement_Components

namespace PathsTreesFlowers.Duality.Supplement

open EdmondsMatching65.Polyhedron (IsMatching)

theorem components_3_5 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M₁ M₂ : Finset E) (h₁ : IsMatching G M₁) (h₂ : IsMatching G M₂)
    (C : Sub G) (hC : IsEdgeComponent G ((M₁ \ M₂) ∪ (M₂ \ M₁)) C) :
    (∃ vs es, IsAlternatingPath G M₁ vs es ∧ IsAlternatingPath G M₂ vs es ∧
      C.verts = vs.toFinset ∧ C.edges = es.toFinset ∧
      (∀ v ∈ vs.head?, IsExposed G M₁ v ∨ IsExposed G M₂ v) ∧
      (∀ v ∈ vs.getLast?, IsExposed G M₁ v ∨ IsExposed G M₂ v)) ∨
    (∃ vs es, IsAlternatingCircuit G M₁ vs es ∧ IsAlternatingCircuit G M₂ vs es ∧
      C.verts = vs.toFinset ∧ C.edges = es.toFinset) := by sorry

end PathsTreesFlowers.Duality.Supplement
