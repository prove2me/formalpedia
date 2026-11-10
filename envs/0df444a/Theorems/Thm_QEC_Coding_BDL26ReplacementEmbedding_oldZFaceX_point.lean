-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_oldZFaceX_point
-- name    : QEC.Coding.BDL26ReplacementEmbedding.oldZFaceX_point
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:02:55.78767+00:00
-- url     : https://prove2.me/theorems/5d57f499-9762-4a74-8bcc-ddead469d081
-- title:
--   BDL26 Replacement Embedding: old ZFace X point
-- statement:
--   The actual old-Z face X corner is the contracted diagonal point.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L477-L482
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L477-L482

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

theorem QEC.Coding.BDL26ReplacementEmbedding.oldZFaceX_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (copy : BDL26FiniteTannerSquare.Two) :
    rxZeroPoint P S J (oldZFaceX P S (f, copy)) =
      facePoint P J f (contractionRatio S) (contractionRatio S) := by sorry
