-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rzFaceImage_eq_transpose
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rzFaceImage_eq_transpose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:32:54.807233+00:00
-- url     : https://prove2.me/theorems/08d15a15-172f-4d65-8dac-f8782cfd94e6
-- title:
--   BDL26 Replacement Embedding: rz Face Image eq transpose
-- statement:
--   The materialized RZ image is the RX image on the transpose, with no image assumption.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1216-L1222
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1216-L1222

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rzFaceImage_eq_transpose (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) (f : BDL26RZLocalReplacement.RZFace P S) :
    rzFaceImage P A S J f =
      rxFaceImage (transposePresentation P) S (transposePointMap P J) (rzFaceEquiv P S f) := by sorry
