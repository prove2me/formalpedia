-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_rootMask_RZ_map2_failure
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.rootMask_RZ_map2_failure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:21:34.291769+00:00
-- url     : https://prove2.me/theorems/fc4b1dcc-4baf-4946-b463-ac991ebaac48
-- title:
--   BDL26 Canonical Root Witness Counterexample: root Mask RZ map2 failure
-- statement:
--   Original root-only selected-map2 commutation already fails at the actual top RZ step.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L1961-L1988
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L1961-L1988

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

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.rootMask_RZ_map2_failure (S : OddScale) :
    topWitness S (upper4 S) ≠
      ((indexedDecoderData S 4).selectedMap (3 : StepIndex 4)).map2 (rootMaskMidWord S) := by sorry
