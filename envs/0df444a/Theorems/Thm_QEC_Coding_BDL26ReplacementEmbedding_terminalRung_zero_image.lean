-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_terminalRung_zero_image
-- name    : QEC.Coding.BDL26ReplacementEmbedding.terminalRung_zero_image
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:29:38.084855+00:00
-- url     : https://prove2.me/theorems/65a363b0-cea5-4c9f-b912-a2451885e0b1
-- title:
--   BDL26 Replacement Embedding: terminal Rung zero image
-- statement:
--   Side zero's terminal rung is horizontal; its boundary-rectangle family is vertical.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L651-L657
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L651-L657

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
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem QEC.Coding.BDL26ReplacementEmbedding.terminalRung_zero_image (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (copy : BDL26FiniteTannerSquare.Two) :
    rxFaceImage P S J (terminalRungFace P S f 0 copy) =
      horizontalImage S (faceGrid P S J f) (copy, lastStrip S) := by sorry
