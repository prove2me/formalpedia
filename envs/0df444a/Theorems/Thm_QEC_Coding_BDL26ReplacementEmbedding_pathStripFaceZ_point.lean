-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_pathStripFaceZ_point
-- name    : QEC.Coding.BDL26ReplacementEmbedding.pathStripFaceZ_point
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T01:52:41.290872+00:00
-- url     : https://prove2.me/theorems/35108d12-53d4-48ab-b2d9-dff0a577c8c9
-- title:
--   BDL26 Replacement Embedding: path Strip Face Z point
-- statement:
--   The path-strip Z corner is the genuine Q-local segment midpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1064-L1071
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1064-L1071

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

theorem QEC.Coding.BDL26ReplacementEmbedding.pathStripFaceZ_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (side copy : BDL26FiniteTannerSquare.Two)
    (i : Fin S.half) (endpoint : BDL26FiniteTannerSquare.Two) :
    rxTwoPoint P S J (rxFaceZ P S (pathStripFace P S f side copy i endpoint)) =
      (1 - (2 * (i.val : ℝ) + 1) / S.ell) • J (.q (P.faceQ f side)) +
        ((2 * (i.val : ℝ) + 1) / S.ell) • J (.z (P.faceZ f)) := by sorry
