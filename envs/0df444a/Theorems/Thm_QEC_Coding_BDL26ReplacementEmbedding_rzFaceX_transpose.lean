-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rzFaceX_transpose
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rzFaceX_transpose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:05:30.594789+00:00
-- url     : https://prove2.me/theorems/83552f02-a53a-46b3-8395-01e3fcf734f2
-- title:
--   BDL26 Replacement Embedding: rz Face X transpose
-- statement:
--   The RZ face X endpoint matches the concrete transposed RX Z endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1150-L1158
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1150-L1158

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rzFaceX_transpose (P : TannerSquarePresentation) (S : OddScale)
    (f : BDL26RZLocalReplacement.RZFace P S) :
    BDL26RZLocalReplacement.rzFaceX P S f =
      rxFaceZ (transposePresentation P) S (rzFaceEquiv P S f) := by sorry
