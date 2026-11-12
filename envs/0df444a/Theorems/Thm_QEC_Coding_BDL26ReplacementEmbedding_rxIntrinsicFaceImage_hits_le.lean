-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rxIntrinsicFaceImage_hits_le
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rxIntrinsicFaceImage_hits_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T21:37:30.293482+00:00
-- url     : https://prove2.me/theorems/433ddadb-e8df-47d9-9666-2b9fbee4a3b1
-- title:
--   BDL26 Replacement Embedding: rx Intrinsic Face Image hits le
-- statement:
--   Original local-face labels, not only quadrant labels, inherit the global density bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3811-L3816
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3811-L3816

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
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26ReplacementEmbedding.rxIntrinsicFaceImage_hits_le (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (region : Set E) :
    (familyHits (rxIntrinsicFaceImage P S J x) region).card ≤
      (familyHits (rxFaceImage P S J) region).card := by sorry
