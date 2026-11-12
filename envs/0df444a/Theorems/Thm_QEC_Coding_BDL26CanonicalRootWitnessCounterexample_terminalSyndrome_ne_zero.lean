-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_terminalSyndrome_ne_zero
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.terminalSyndrome_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:06:15.426605+00:00
-- url     : https://prove2.me/theorems/1b28ffa8-eb4b-497a-837b-23071b0e4694
-- title:
--   BDL26 Canonical Root Witness Counterexample: terminal Syndrome ne zero
-- statement:
--   Both terminals exist at every OddScale; no half_pos is involved.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L370-L384
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L370-L384

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

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.terminalSyndrome_ne_zero (S : OddScale) (q : (state S 2).presentation.Q)
    (z : (state S 2).presentation.Z) (hqz : (state S 2).presentation.qz q z = true) :
    terminalSyndrome S q z hqz ≠ 0 := by sorry
