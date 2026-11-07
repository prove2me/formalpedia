-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CayleyClique_card_neighborVertices_schreier_le
-- name    : QEC.Coding.HighDimensionalExpander.CayleyClique.card_neighborVertices_schreier_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:58:23.906696+00:00
-- url     : https://prove2.me/theorems/2864b2b2-4ce9-4c09-a866-8ddf99f43d4e
-- title:
--   Cayley Clique: card neighbor Vertices schreier le
-- statement:
--   The Cayley Clique construction uses the card neighbor Vertices schreier le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/CayleyClique.lean#L355-L358
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/CayleyClique.lean#L355-L358

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

theorem QEC.Coding.HighDimensionalExpander.CayleyClique.card_neighborVertices_schreier_le (S : Finset Γ) (x : X) :
    (neighborVertices (schreierGraph (X := X) (S : Set Γ)) x).card ≤ 2 * S.card := by sorry
