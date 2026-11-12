-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_oldZFaceX_shared_point
-- name    : QEC.Coding.BDL26ReplacementEmbedding.oldZFaceX_shared_point
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T20:49:34.895206+00:00
-- url     : https://prove2.me/theorems/901ff95c-9996-4c40-b652-a97333b9150d
-- title:
--   BDL26 Replacement Embedding: old ZFace X shared point
-- statement:
--   Shared old-Z X corners agree geometrically because their actual global vertex agrees.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L524-L529
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L524-L529

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

theorem QEC.Coding.BDL26ReplacementEmbedding.oldZFaceX_shared_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f g : P.Face) (copy : BDL26FiniteTannerSquare.Two)
    (hx : P.faceX f = P.faceX g) (hz : P.faceZ f = P.faceZ g) :
    rxZeroPoint P S J (oldZFaceX P S (f, copy)) =
      rxZeroPoint P S J (oldZFaceX P S (g, copy)) := by sorry
