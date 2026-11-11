-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rzIntrinsicFaceImage_hits_le
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rzIntrinsicFaceImage_hits_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T21:38:56.549511+00:00
-- url     : https://prove2.me/theorems/82036ee4-307a-4404-b8f0-ecb7a70b8f07
-- title:
--   BDL26 Replacement Embedding: rz Intrinsic Face Image hits le
-- statement:
--   The corresponding density restriction for the existing RZ intrinsic face carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3824-L3829
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3824-L3829

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rzIntrinsicFaceImage_hits_le (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) (z : P.Z) (region : Set E) :
    (familyHits (rzIntrinsicFaceImage P A S J z) region).card ≤
      (familyHits (rzFaceImage P A S J) region).card := by sorry
