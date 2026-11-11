-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_lowerSyndromeRaw_nonzero
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.lowerSyndromeRaw_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:56:20.196201+00:00
-- url     : https://prove2.me/theorems/c2424fdb-7391-43bb-94dd-43c757c4ab58
-- title:
--   BDL26 Uniform History Obstruction: lower Syndrome Raw nonzero
-- statement:
--   The BDL26 Uniform History Obstruction construction uses the lower Syndrome Raw nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWitness.lean#L61-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWitness.lean#L61-L84

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks
open BDL26OwnerParentObstruction BDL26ReplacementSupport BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open BDL26XLocalRadialParity BDL26XLocalConnectingWeight
open MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26UniformHistoryObstruction.lowerSyndromeRaw_nonzero (S : OddScale) (n : Nat) : (lowerSyndromeRaw S n) ≠ 0 := by sorry
