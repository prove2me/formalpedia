-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_triangleAltitudeDirection_inner_side
-- name    : QEC.Coding.BDL26ReplacementEmbedding.triangleAltitudeDirection_inner_side
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:34:18.609951+00:00
-- url     : https://prove2.me/theorems/ee3092eb-051c-47c6-91fe-9fe362545db3
-- title:
--   BDL26 Replacement Embedding: triangle Altitude Direction inner side
-- statement:
--   The BDL26 Replacement Embedding construction uses the triangle Altitude Direction inner side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1326-L1343
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1326-L1343

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26ReplacementEmbedding.triangleAltitudeDirection_inner_side {b c : E}
    (hb : b ≠ 0) (hc : triangleAltitudeVector b c ≠ 0) :
    ⟪triangleUnitDirection (triangleAltitudeVector b c), c⟫_ℝ =
      ‖triangleAltitudeVector b c‖ := by sorry
