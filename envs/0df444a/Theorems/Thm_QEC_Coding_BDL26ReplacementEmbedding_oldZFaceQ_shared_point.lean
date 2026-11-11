-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_oldZFaceQ_shared_point
-- name    : QEC.Coding.BDL26ReplacementEmbedding.oldZFaceQ_shared_point
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T20:49:43.969204+00:00
-- url     : https://prove2.me/theorems/34646841-6aa0-4479-a4d6-38c116711ebb
-- title:
--   BDL26 Replacement Embedding: old ZFace Q shared point
-- statement:
--   Shared old-Z Q corners agree using actual Q/Z tags, independently of the face label.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L532-L538
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L532-L538

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

theorem QEC.Coding.BDL26ReplacementEmbedding.oldZFaceQ_shared_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f g : P.Face)
    (a b copy : BDL26FiniteTannerSquare.Two)
    (hq : P.faceQ f a = P.faceQ g b) (hz : P.faceZ f = P.faceZ g) :
    rxOnePoint P S J (oldZFaceQ P S a (f, copy)) =
      rxOnePoint P S J (oldZFaceQ P S b (g, copy)) := by sorry
