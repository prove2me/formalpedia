-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CayleyClique_extensionVertices_subset_neighborVertices
-- name    : QEC.Coding.HighDimensionalExpander.CayleyClique.extensionVertices_subset_neighborVertices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:57:40.744129+00:00
-- url     : https://prove2.me/theorems/3325cb79-bed6-4bca-9285-70733d7108bc
-- title:
--   Cayley Clique: extension Vertices subset neighbor Vertices
-- statement:
--   The Cayley Clique construction uses the extension Vertices subset neighbor Vertices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/CayleyClique.lean#L161-L170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/CayleyClique.lean#L161-L170

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

theorem QEC.Coding.HighDimensionalExpander.CayleyClique.extensionVertices_subset_neighborVertices
    (G : SimpleGraph V) (s : Finset V) {x : V} (hx : x ∈ s) :
    extensionVertices (cliqueComplex G) s ⊆ neighborVertices G x := by sorry
