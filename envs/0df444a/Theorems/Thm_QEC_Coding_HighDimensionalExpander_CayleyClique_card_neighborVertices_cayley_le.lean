-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CayleyClique_card_neighborVertices_cayley_le
-- name    : QEC.Coding.HighDimensionalExpander.CayleyClique.card_neighborVertices_cayley_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:58:01.544109+00:00
-- url     : https://prove2.me/theorems/4da8ccf2-e1a5-4dcc-8368-f9dcd66f9af7
-- title:
--   Cayley Clique: card neighbor Vertices cayley le
-- statement:
--   The Cayley Clique construction uses the card neighbor Vertices cayley le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/CayleyClique.lean#L242-L245
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/CayleyClique.lean#L242-L245

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
variable {Γ : Type u} [Group Γ]
variable [Fintype Γ] [DecidableEq Γ]

theorem QEC.Coding.HighDimensionalExpander.CayleyClique.card_neighborVertices_cayley_le (S : Finset Γ) (x : Γ) :
    (neighborVertices (SimpleGraph.mulCayley (S : Set Γ)) x).card ≤ 2 * S.card := by sorry
