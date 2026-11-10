-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_doubleCylinderFace_total
-- name    : QEC.Coding.BDL26ReplacementEmbedding.doubleCylinderFace_total
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:27:04.766211+00:00
-- url     : https://prove2.me/theorems/1a37d611-ac7e-43ed-a2dd-0d274730f43a
-- title:
--   BDL26 Replacement Embedding: double Cylinder Face total
-- statement:
--   The local doubled-face count is exact, including boundary rectangles.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L55-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L55-L62

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

theorem QEC.Coding.BDL26ReplacementEmbedding.doubleCylinderFace_total (P : TannerSquarePresentation) (S : OddScale) :
    (∑ x : P.X, Fintype.card (DoubleCylinderFace P x S)) =
      (2 * S.half ^ 2 + 2 * S.half) * Fintype.card P.Face := by sorry
