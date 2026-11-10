-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_pathStrip_boundaryUnit_upper
-- name    : QEC.Coding.BDL26ReplacementEmbedding.pathStrip_boundaryUnit_upper
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T02:40:31.455038+00:00
-- url     : https://prove2.me/theorems/907ae4c0-9900-4ccf-a1b3-4458a3717b64
-- title:
--   BDL26 Replacement Embedding: path Strip boundary Unit upper
-- statement:
--   The final row uses the usual Q order and the same actual fine unit steps.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3130-L3144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3130-L3144

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

theorem QEC.Coding.BDL26ReplacementEmbedding.pathStrip_boundaryUnit_upper (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width : ℝ} (hgeo : IncomingFaceGeometry P S J lower width)
    (f : P.Face) (copy : BDL26FiniteTannerSquare.Two) (i : Fin S.half)
    (a : BDL26FiniteTannerSquare.Two) :
    rxFaceBoundaryUnit P S J (pathStripFace P S f 1 copy i a) := by sorry
