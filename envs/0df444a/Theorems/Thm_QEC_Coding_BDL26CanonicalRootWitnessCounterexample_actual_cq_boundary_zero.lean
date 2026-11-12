-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_actual_cq_boundary_zero
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actual_cq_boundary_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:04:53.978254+00:00
-- url     : https://prove2.me/theorems/da5eb3bc-29cc-464b-ad35-18a6844b2b7f
-- title:
--   BDL26 Canonical Root Witness Counterexample: actual cq boundary zero
-- statement:
--   The corresponding fact for the actual Q selector after the actual X step.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L232-L258
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L232-L258

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

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actual_cq_boundary_zero (S : OddScale) (sigma : Word3 S)
    (hq : ∀ q, restrictWordLinear ((LQ S).syndromeRegion q)
      (rxSigmaAfterCx (A S) sigma) = 0)
    (q : (state S 2).presentation.Q) :
    d3 S (cqComponentTotal (A S) sigma q) = 0 := by sorry
