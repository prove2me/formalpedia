-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_actualRXHits_card_eq_flat
-- name    : QEC.Coding.BDL26ReplacementEmbedding.actualRXHits_card_eq_flat
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:37:36.775835+00:00
-- url     : https://prove2.me/theorems/a5c453d5-54dc-4796-9533-0e2766da063a
-- title:
--   BDL26 Replacement Embedding: actual RXHits card eq flat
-- statement:
--   Reindexing the actual geometric hit set preserves all labeled multiplicities.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1842-L1857
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1842-L1857

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
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem QEC.Coding.BDL26ReplacementEmbedding.actualRXHits_card_eq_flat (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (region : Set E) :
    (familyHits (rxFaceImage P S J) region).card =
      (familyHits (actualFlatImage P S J) region).card := by sorry
