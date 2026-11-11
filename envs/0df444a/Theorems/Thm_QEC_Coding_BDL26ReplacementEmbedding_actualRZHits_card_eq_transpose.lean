-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_actualRZHits_card_eq_transpose
-- name    : QEC.Coding.BDL26ReplacementEmbedding.actualRZHits_card_eq_transpose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:40:33.692716+00:00
-- url     : https://prove2.me/theorems/c563306a-5998-42bf-8a8b-550aefdc0f2e
-- title:
--   BDL26 Replacement Embedding: actual RZHits card eq transpose
-- statement:
--   Every actual RZ label is counted through the proved materialized transpose equivalence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2926-L2943
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2926-L2943

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26ReplacementEmbedding.actualRZHits_card_eq_transpose (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (J : Vertex P → E) (region : Set E) :
    (familyHits (rzFaceImage P A S J) region).card =
      (familyHits (rxFaceImage (transposePresentation P) S (transposePointMap P J)) region).card := by sorry
