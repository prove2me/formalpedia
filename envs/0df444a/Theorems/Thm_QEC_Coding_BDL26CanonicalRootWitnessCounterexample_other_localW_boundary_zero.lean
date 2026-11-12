-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_other_localW_boundary_zero
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.other_localW_boundary_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:07:29.292931+00:00
-- url     : https://prove2.me/theorems/60a1550b-5eaf-423d-9142-4aaecc0da6f5
-- title:
--   BDL26 Canonical Root Witness Counterexample: other local W boundary zero
-- statement:
--   The BDL26 Canonical Root Witness Counterexample construction uses the other local W boundary zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L601-L620
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L601-L620

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

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.other_localW_boundary_zero (S : OddScale) (q : (state S 2).presentation.Q)
    (hq : q ≠ q2 S) :
    d3 S (extendWordLinear ((LQ S).correctionRegion q) (localW S q)) = 0 := by sorry
