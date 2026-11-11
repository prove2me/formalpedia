-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZErrorPullback_zero_run_coarse
-- name    : QEC.Coding.BDL26RZErrorPullback.zero_run_coarse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:08:39.59131+00:00
-- url     : https://prove2.me/theorems/4e67b361-4a8e-47b1-9ebf-c54abf9c27d9
-- title:
--   BDL26 RZError Pullback: zero run coarse
-- statement:
--   Zero coarse syndrome is established independently of the correction selector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZErrorPullback.lean#L227-L230
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZErrorPullback.lean#L227-L230

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Indexed
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZErrorPullback
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge BDL26RZCohomology BDL26AlternatingCochain
open MultiscaleDecoder BDL26OwnerIncidenceMasks
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26RZErrorPullback.zero_run_coarse (h : ¬ i.val % 2 = 0) : (run S depth i h 0).coarse.val = 0 := by sorry
