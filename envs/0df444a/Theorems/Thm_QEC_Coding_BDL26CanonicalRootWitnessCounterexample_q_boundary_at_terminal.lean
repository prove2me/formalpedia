-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_q_boundary_at_terminal
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.q_boundary_at_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:10:40.159469+00:00
-- url     : https://prove2.me/theorems/fe66a650-1d70-4d81-8b2c-68095549a304
-- title:
--   BDL26 Canonical Root Witness Counterexample: q boundary at terminal
-- statement:
--   Literal terminal evaluation in the actual physical Q chart.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L773-L791
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L773-L791

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

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.q_boundary_at_terminal (S : OddScale) (q : (state S 2).presentation.Q)
    (w : LocalQWord S q) (z : (state S 2).presentation.Z)
    (hqz : (state S 2).presentation.qz q z = true) (b : Fin 2) :
    d3 S (extendWordLinear ((LQ S).correctionRegion q) w)
      ((A S).induced.zPairEquiv (z,b)).val = w (terminalVertex S q z hqz b) := by sorry
