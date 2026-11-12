-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_actual_Q_flow_raw_value
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actual_Q_flow_raw_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:10:27.625725+00:00
-- url     : https://prove2.me/theorems/5af6473b-01cf-4461-801d-bfe353f471c5
-- title:
--   BDL26 Canonical Root Witness Counterexample: actual Q flow raw value
-- statement:
--   Only the actual transported flow projection is normalized in this identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L763-L770
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L763-L770

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

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actual_Q_flow_raw_value (S : OddScale) (q : (state S 2).presentation.Q)
    (w : LocalQWord S q) (z : (state S 2).presentation.Z) (b : Fin 2) :
    (A S).contract.support_decomposition.cqFlow q w
        ((A S).induced.zPairEquiv (z,b)).val =
      qFlow (state S 2).presentation S q
        (fun v => w (rxQVertexEquiv S 4 (2 : StepIndex 4) (by decide) q v))
        (Sum.inr (z,b)) := by sorry
