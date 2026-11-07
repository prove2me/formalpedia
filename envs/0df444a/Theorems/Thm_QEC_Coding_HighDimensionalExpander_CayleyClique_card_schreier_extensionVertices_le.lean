-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CayleyClique_card_schreier_extensionVertices_le
-- name    : QEC.Coding.HighDimensionalExpander.CayleyClique.card_schreier_extensionVertices_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:52:10.684667+00:00
-- url     : https://prove2.me/theorems/893c91c3-f42e-4437-b5b2-e7289a888a2b
-- title:
--   Cayley Clique: card schreier extension Vertices le
-- statement:
--   The number of one-vertex cofaces of a nonempty Schreier-clique face is
--   bounded directly by twice the number of selected generators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/CayleyClique.lean#L363-L369
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/CayleyClique.lean#L363-L369

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
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
variable [Fintype X] [DecidableEq X] [DecidableEq Γ]
omit [DecidableEq Γ]

theorem QEC.Coding.HighDimensionalExpander.CayleyClique.card_schreier_extensionVertices_le
    (S : Finset Γ) (s : Finset X) {x : X} (hx : x ∈ s) :
    (extensionVertices (schreierCliqueComplex (X := X) (S : Set Γ)) s).card ≤
      2 * S.card := by sorry
