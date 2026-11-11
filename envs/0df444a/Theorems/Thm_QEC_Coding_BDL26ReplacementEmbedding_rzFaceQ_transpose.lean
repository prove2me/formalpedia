-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rzFaceQ_transpose
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rzFaceQ_transpose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:06:11.973353+00:00
-- url     : https://prove2.me/theorems/d3cf083f-fe56-453b-af6e-854671b3a8fb
-- title:
--   BDL26 Replacement Embedding: rz Face Q transpose
-- statement:
--   Both ordered Q endpoints also match their actual transposed materialized tags.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1188-L1203
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1188-L1203

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rzFaceQ_transpose (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (f : BDL26RZLocalReplacement.RZFace P S)
    (corner : BDL26FiniteTannerSquare.Two) :
    BDL26RZLocalReplacement.rzFaceQ P A S f corner =
      rxFaceQ (transposePresentation P) S (rzFaceEquiv P S f) corner := by sorry
