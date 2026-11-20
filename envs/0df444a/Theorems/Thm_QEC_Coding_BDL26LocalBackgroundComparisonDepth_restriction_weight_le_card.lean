-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonDepth_restriction_weight_le_card
-- name    : QEC.Coding.BDL26LocalBackgroundComparisonDepth.restriction_weight_le_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:31:14.415068+00:00
-- url     : https://prove2.me/theorems/aced4b23-d323-414c-8c09-5b2d453b1893
-- title:
--   BDL26 Local Background Comparison Depth: restriction weight le card
-- statement:
--   Literal restriction cannot have more nonzero coordinates than its mask.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonDepth.lean#L163-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonDepth.lean#L163-L172

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonResponse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalBackgroundComparisonDepth
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual BDL26RZMap1CoordinateBridge
open BDL26LocalBackgroundComparisonResponse
open scoped Classical BigOperators

theorem QEC.Coding.BDL26LocalBackgroundComparisonDepth.restriction_weight_le_card (S : OddScale) (n : Nat)
    (g : W S n) (A : Finset (Q S n)) :
    HammingWeight (backgroundRestriction S n g A) ≤ A.card := by sorry
