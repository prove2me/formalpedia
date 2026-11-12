-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_terminal_solution_imbalance
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.terminal_solution_imbalance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:07:00.539916+00:00
-- url     : https://prove2.me/theorems/495df952-86d4-41b1-8fad-eb0d9098a79e
-- title:
--   BDL26 Canonical Root Witness Counterexample: terminal solution imbalance
-- statement:
--   Every genuine selected solution of the terminal query has the same
--   copy imbalance. It may be the indicator or its complement.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L404-L424
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L404-L424

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

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.terminal_solution_imbalance (S : OddScale) (q : (state S 2).presentation.Q)
    (z : (state S 2).presentation.Z) (hqz : (state S 2).presentation.qz q z = true)
    (w : LocalQWord S q)
    (hw : (A S).contract.rx_local_complexes.cqDelta1 q w =
      terminalSyndrome S q z hqz) :
    w (terminalVertex S q z hqz 0) + w (terminalVertex S q z hqz 1) = 1 := by sorry
