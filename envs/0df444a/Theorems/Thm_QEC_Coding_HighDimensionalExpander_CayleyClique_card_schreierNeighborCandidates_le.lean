-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CayleyClique_card_schreierNeighborCandidates_le
-- name    : QEC.Coding.HighDimensionalExpander.CayleyClique.card_schreierNeighborCandidates_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:58:10.838568+00:00
-- url     : https://prove2.me/theorems/d461cf0f-f431-4d43-b768-467aad13c96b
-- title:
--   Cayley Clique: card schreier Neighbor Candidates le
-- statement:
--   The Cayley Clique construction uses the card schreier Neighbor Candidates le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/CayleyClique.lean#L345-L352
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/CayleyClique.lean#L345-L352

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
omit [Fintype X] [DecidableEq Γ]

theorem QEC.Coding.HighDimensionalExpander.CayleyClique.card_schreierNeighborCandidates_le (S : Finset Γ) (x : X) :
    (schreierNeighborCandidates S x).card ≤ 2 * S.card := by sorry
