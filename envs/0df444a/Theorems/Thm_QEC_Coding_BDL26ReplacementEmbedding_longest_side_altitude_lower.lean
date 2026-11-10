-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_longest_side_altitude_lower
-- name    : QEC.Coding.BDL26ReplacementEmbedding.longest_side_altitude_lower
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:35:48.078018+00:00
-- url     : https://prove2.me/theorems/fa047a67-543b-4f12-bae6-5c8b225bdd96
-- title:
--   BDL26 Replacement Embedding: longest side altitude lower
-- statement:
--   The foot on a longest side lies on that segment, so the source segment-width
--   bound applies to this altitude even when the triangle is obtuse.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1519-L1538
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1519-L1538

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

theorem QEC.Coding.BDL26ReplacementEmbedding.longest_side_altitude_lower {b c : E} {delta : ℝ} (hb : b ≠ 0)
    (hc : ‖c‖ ≤ ‖b‖) (hbc : ‖c - b‖ ≤ ‖b‖)
    (hwidth : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → delta ≤ ‖c - t • b‖) :
    delta ≤ ‖triangleAltitudeVector b c‖ := by sorry
