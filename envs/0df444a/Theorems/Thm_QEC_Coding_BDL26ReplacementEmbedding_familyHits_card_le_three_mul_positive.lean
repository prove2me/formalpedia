-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_familyHits_card_le_three_mul_positive
-- name    : QEC.Coding.BDL26ReplacementEmbedding.familyHits_card_le_three_mul_positive
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T13:48:33.70441+00:00
-- url     : https://prove2.me/theorems/af55ae3e-0922-4a05-b45c-e30f931d895a
-- title:
--   BDL26 Replacement Embedding: family Hits card le three mul positive
-- statement:
--   Geometric charging works for the actual positive images as well as the
--   canonical flat triangulation. Only proved image containments are needed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbedding.lean#L207-L228
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbedding.lean#L207-L228

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open BDL26FiniteTannerSquare
open scoped BigOperators

theorem QEC.Coding.BDL26ReplacementEmbedding.familyHits_card_le_three_mul_positive {Owner E : Type*} [Fintype Owner]
    (S : OddScale) (images : Owner × FlatCell S → Set E) (region : Set E)
    (himage : ∀ owner cell, images (owner, cell) ⊆
      images (owner, .inl (charge S cell))) :
    (familyHits images region).card ≤
      3 * (familyHits (fun p : Owner × PositiveCell S => images (p.1, .inl p.2)) region).card := by sorry
