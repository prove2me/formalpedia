-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_actual_cx_boundary_zero
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actual_cx_boundary_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:04:35.607605+00:00
-- url     : https://prove2.me/theorems/331d8ddf-e81b-4b12-ba15-1173f9c685bd
-- title:
--   BDL26 Canonical Root Witness Counterexample: actual cx boundary zero
-- statement:
--   A zero local query forces the actual X *boundary* to vanish.
--   The actual chosen closed correction is retained and is not asserted zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L196-L220
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L196-L220

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

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actual_cx_boundary_zero (S : OddScale) (sigma : Word3 S)
    (hx : ∀ x, restrictWordLinear ((LX S).syndromeRegion x) sigma = 0)
    (x : (state S 2).presentation.X) :
    d3 S (cxComponentTotal (A S) sigma x) = 0 := by sorry
