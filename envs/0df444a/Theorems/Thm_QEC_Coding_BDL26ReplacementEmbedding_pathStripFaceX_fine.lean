-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_pathStripFaceX_fine
-- name    : QEC.Coding.BDL26ReplacementEmbedding.pathStripFaceX_fine
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T02:37:50.686288+00:00
-- url     : https://prove2.me/theorems/ef5c0ff1-abbf-4bde-a93c-0b68537045fd
-- title:
--   BDL26 Replacement Embedding: path Strip Face X fine
-- statement:
--   The X corner lies on the inner edge of the final fine-grid column.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1909-L1922
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1909-L1922

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

theorem QEC.Coding.BDL26ReplacementEmbedding.pathStripFaceX_fine (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (copy : BDL26FiniteTannerSquare.Two)
    (i : Fin S.half) (endpoint : BDL26FiniteTannerSquare.Two) :
    rxZeroPoint P S J (rxFaceX P S (pathStripFace P S f 0 copy i endpoint)) =
      facePoint P J f (contractionRatio S) (2 * ((gridEndpoint i endpoint).val : ℝ) / S.ell) := by sorry
