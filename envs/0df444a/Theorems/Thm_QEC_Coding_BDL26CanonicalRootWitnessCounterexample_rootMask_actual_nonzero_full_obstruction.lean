-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_rootMask_actual_nonzero_full_obstruction
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.rootMask_actual_nonzero_full_obstruction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:46:29.21157+00:00
-- url     : https://prove2.me/theorems/41a21a7a-55a4-468b-9eed-b576f0b05587
-- title:
--   BDL26 Canonical Root Witness Counterexample: root Mask actual nonzero full obstruction
-- statement:
--   The exact valid depth-four input has nonzero actual C2 readout and both original-root obstructions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L1991-L1999
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L1991-L1999

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

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.rootMask_actual_nonzero_full_obstruction (S : OddScale) :
    (BDL26CanonicalHistoryMarks.baseInput S 2 (upper4 S)).val ≠ 0 ∧
      topWitness S (upper4 S) ≠
        ((indexedDecoderData S 4).selectedMap (3 : StepIndex 4)).map2 (rootMaskMidWord S) ∧
      topWitness S (upper4 S) ∉ LinearMap.range ((CF S).coboundary1 level4) := by sorry
