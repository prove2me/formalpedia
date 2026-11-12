-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_actualQSection_zero_boundary
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actualQSection_zero_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:34:41.134465+00:00
-- url     : https://prove2.me/theorems/b3cb2426-db80-4527-bf0d-6f299cf5fd80
-- title:
--   BDL26 Canonical Root Witness Counterexample: actual QSection zero boundary
-- statement:
--   Zero-query section values need not vanish, but their global boundary does.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L427-L440
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L427-L440

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

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actualQSection_zero_boundary (S : OddScale) (q : (state S 2).presentation.Q)
    (ht : (0 : LocalQSyndrome S q) ∈
      LinearMap.range ((A S).contract.rx_local_complexes.cqDelta1 q)) :
    d3 S (extendWordLinear ((LQ S).correctionRegion q)
      (actualQSection S q 0 ht)) = 0 := by sorry
