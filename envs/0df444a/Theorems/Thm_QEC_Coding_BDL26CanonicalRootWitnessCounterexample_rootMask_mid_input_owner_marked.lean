-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_rootMask_mid_input_owner_marked
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.rootMask_mid_input_owner_marked
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:10:32.18824+00:00
-- url     : https://prove2.me/theorems/530eb983-0cbc-4a24-a5fc-043056b72445
-- title:
--   BDL26 Canonical Root Witness Counterexample: root Mask mid input owner marked
-- statement:
--   The real stored C3 input, rather than a supplied root certificate, marks its owner.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L1868-L1887
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L1868-L1887

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

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.rootMask_mid_input_owner_marked (S : OddScale)
    (p : FamilyZ S 4 level3) (hp : (lower3 S).val p ≠ 0) :
    actualMidNode S (BDL26CanonicalHistoryMarks.syndromeOwner S 2 (0 : StepIndex 2) p) ∈
      BDL26CanonicalHistoryMarks.marks S 2 (upper4 S) := by sorry
