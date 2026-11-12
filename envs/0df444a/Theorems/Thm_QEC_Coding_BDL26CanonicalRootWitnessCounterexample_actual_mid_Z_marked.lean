-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_actual_mid_Z_marked
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actual_mid_Z_marked
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:02:11.346909+00:00
-- url     : https://prove2.me/theorems/28ef4d74-9990-46a4-a33e-2129bcc635bd
-- title:
--   BDL26 Canonical Root Witness Counterexample: actual mid Z marked
-- statement:
--   The actual stored mid-level input supplies the actual syndrome-owner mark.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L1522-L1581
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L1522-L1581

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
set_option autoImplicit false
attribute [local irreducible] QEC.Coding.BDL26CanonicalHistoryMarks.rootComponent
open QEC QEC.Coding QEC.Coding.BDL26CanonicalRootWitnessCounterexample
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26ReplacementSupport
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable section
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open BDL26RXLocalReplacement BDL26RXStagedRestriction

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actual_mid_Z_marked (S : OddScale)
    (sigma : BDL26CanonicalHistoryMarks.Input S 2)
    (hmid : BDL26CanonicalHistoryMarks.inputAt S 2 sigma
      (1 : LevelIndex 2) = lower3 S) :
    actualMidNode S (zVertex S 2 (r2 S)) ∈
      BDL26CanonicalHistoryMarks.marks S 2 sigma := by sorry
