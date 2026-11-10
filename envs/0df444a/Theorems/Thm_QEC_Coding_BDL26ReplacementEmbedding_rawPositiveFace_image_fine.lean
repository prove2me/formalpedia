-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rawPositiveFace_image_fine
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rawPositiveFace_image_fine
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T02:39:50.251558+00:00
-- url     : https://prove2.me/theorems/0de171d7-4ea0-48bd-99fe-8a5e0638e2ac
-- title:
--   BDL26 Replacement Embedding: raw Positive Face image fine
-- statement:
--   Constructor-by-constructor image equality for the whole actual positive family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2554-L2567
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2554-L2567

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26ReplacementEmbedding.rawPositiveFace_image_fine (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (c : RawPositiveCell S) :
    rxFaceImage P S J (rawPositiveFace P S f c) =
      fineQuadrantImage P S J f (rawFineInteger S c.2.1) (rawFineInteger S c.2.2)
        (fineEndpointBit S c.2.1) (fineEndpointBit S c.2.2) := by sorry
