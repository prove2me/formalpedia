-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_actual_cq_reselect
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actual_cq_reselect
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:06:49.294808+00:00
-- url     : https://prove2.me/theorems/9036474b-690a-490b-97b4-fd0737317147
-- title:
--   BDL26 Canonical Root Witness Counterexample: actual cq reselect
-- statement:
--   Equal literal cleaned queries select the same real Classical.choose value.
--   The private cqWitnessAt is unfolded definitionally; no uniqueness of solutions
--   is assumed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L445-L486
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L445-L486

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

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actual_cq_reselect (S : OddScale) (sigma : Word3 S)
    (q : (state S 2).presentation.Q) (t : LocalQSyndrome S q)
    (ht : t ∈ LinearMap.range ((A S).contract.rx_local_complexes.cqDelta1 q))
    (hquery : restrictWordLinear ((LQ S).syndromeRegion q)
      (rxSigmaAfterCx (A S) sigma) = t) :
    cqComponentTotal (A S) sigma q =
      extendWordLinear ((LQ S).correctionRegion q) (actualQSection S q t ht) := by sorry
