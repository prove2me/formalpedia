-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_retained_Z_actual_root_member
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.retained_Z_actual_root_member
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:44:43.003037+00:00
-- url     : https://prove2.me/theorems/5662f7fc-de0a-4466-8e36-c258940f5122
-- title:
--   BDL26 Canonical Root Witness Counterexample: retained Z actual root member
-- statement:
--   The BDL26 Canonical Root Witness Counterexample construction uses the retained Z actual root member property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L1607-L1628
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L1607-L1628

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

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.retained_Z_actual_root_member (S : OddScale)
    (sigma : BDL26CanonicalHistoryMarks.Input S 2)
    (hbase : BDL26CanonicalHistoryMarks.baseInput S 2 sigma = gamma2 S)
    (hmid : BDL26CanonicalHistoryMarks.inputAt S 2 sigma
      (1 : LevelIndex 2) = lower3 S) :
    @Membership.mem.{0, 0} (BDL26CanonicalHistoryMarks.Node S 2)
      (Finset (BDL26CanonicalHistoryMarks.Node S 2))
      (@SetLike.instMembership.{0, 0} (Finset (BDL26CanonicalHistoryMarks.Node S 2))
        (BDL26CanonicalHistoryMarks.Node S 2)
        (@Finset.instSetLike.{0} (BDL26CanonicalHistoryMarks.Node S 2)))
      (BDL26CanonicalHistoryMarks.rootComponent S 2 sigma)
      (actualMidNode S (zVertex S 2 (r2 S))) := by sorry
