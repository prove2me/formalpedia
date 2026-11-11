-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_oldZ_boundaryUnit
-- name    : QEC.Coding.BDL26ReplacementEmbedding.oldZ_boundaryUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:42:28.458482+00:00
-- url     : https://prove2.me/theorems/ed90f799-4b7f-4d5b-bbd6-a1b9355c1195
-- title:
--   BDL26 Replacement Embedding: old Z boundary Unit
-- statement:
--   The final old-Z face is the last actual fine quadrant, for each coincident copy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3147-L3159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3147-L3159

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

theorem QEC.Coding.BDL26ReplacementEmbedding.oldZ_boundaryUnit (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width : ℝ} (hgeo : IncomingFaceGeometry P S J lower width)
    (f : P.Face) (copy : BDL26FiniteTannerSquare.Two) :
    rxFaceBoundaryUnit P S J (.inr (.inr (f, copy))) := by sorry
