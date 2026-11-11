-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_incomingFaceGeometry_of_source_bounds
-- name    : QEC.Coding.BDL26ReplacementEmbedding.incomingFaceGeometry_of_source_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:41:53.631754+00:00
-- url     : https://prove2.me/theorems/15dfdb64-d04e-489d-bd49-bc4eb4b8593d
-- title:
--   BDL26 Replacement Embedding: incoming Face Geometry of source bounds
-- statement:
--   Perturbation bounds at the unrounded source length imply the input geometry
--   for its genuine larger odd replacement scale.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3055-L3068
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3055-L3068

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26ReplacementEmbedding.incomingFaceGeometry_of_source_bounds (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {L lower width : ℝ} (hL : L ≤ S.ell)
    (hsideLo : ∀ f side, lower ≤ ‖J (.q (P.faceQ f side)) - J (.x (P.faceX f))‖)
    (hdiagLo : ∀ f, lower ≤ ‖J (.z (P.faceZ f)) - J (.x (P.faceX f))‖)
    (hoppLo : ∀ f side, lower ≤ ‖J (.z (P.faceZ f)) - J (.q (P.faceQ f side))‖)
    (hsideUp : ∀ f side, ‖J (.q (P.faceQ f side)) - J (.x (P.faceX f))‖ ≤ L)
    (hdiagUp : ∀ f, ‖J (.z (P.faceZ f)) - J (.x (P.faceX f))‖ ≤ L)
    (hoppUp : ∀ f side, ‖J (.z (P.faceZ f)) - J (.q (P.faceQ f side))‖ ≤ L)
    (hthin : ∀ f side, TriangleWidthAtLeast
      (J (.q (P.faceQ f side)) - J (.x (P.faceX f)))
      (J (.z (P.faceZ f)) - J (.x (P.faceX f))) width) :
    IncomingFaceGeometry P S J lower width := by sorry
