-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CayleyClique_card_extensionVertices_le_neighbors
-- name    : QEC.Coding.HighDimensionalExpander.CayleyClique.card_extensionVertices_le_neighbors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:57:37.370949+00:00
-- url     : https://prove2.me/theorems/a7b4a98a-6729-4a63-ace8-bf47603b873d
-- title:
--   Cayley Clique: card extension Vertices le neighbors
-- statement:
--   Once a face has a vertex, the number of one-vertex cofaces is bounded by
--   the degree of that vertex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/CayleyClique.lean#L174-L177
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/CayleyClique.lean#L174-L177

import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CayleyClique
open Finset
universe u v
variable {V : Type u} {W : Type v}
variable [Fintype V] [DecidableEq V]

theorem QEC.Coding.HighDimensionalExpander.CayleyClique.card_extensionVertices_le_neighbors
    (G : SimpleGraph V) (s : Finset V) {x : V} (hx : x ∈ s) :
    (extensionVertices (cliqueComplex G) s).card ≤ (neighborVertices G x).card := by sorry
