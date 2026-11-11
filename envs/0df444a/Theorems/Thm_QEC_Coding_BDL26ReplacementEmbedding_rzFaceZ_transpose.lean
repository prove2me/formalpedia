-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rzFaceZ_transpose
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rzFaceZ_transpose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:06:08.19179+00:00
-- url     : https://prove2.me/theorems/5a715e69-b826-4794-a8f1-bed79d658dc0
-- title:
--   BDL26 Replacement Embedding: rz Face Z transpose
-- statement:
--   The RZ face Z endpoint matches the concrete transposed RX X endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1161-L1185
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1161-L1185

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rzFaceZ_transpose (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (f : BDL26RZLocalReplacement.RZFace P S) :
    BDL26RZLocalReplacement.rzFaceZ P A S f =
      rxFaceX (transposePresentation P) S (rzFaceEquiv P S f) := by sorry
