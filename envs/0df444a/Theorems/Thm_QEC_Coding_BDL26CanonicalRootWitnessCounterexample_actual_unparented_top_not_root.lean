-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_actual_unparented_top_not_root
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actual_unparented_top_not_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:08:23.197363+00:00
-- url     : https://prove2.me/theorems/e947d4bd-ccd0-4aa8-ac86-1f8fba0384cc
-- title:
--   BDL26 Canonical Root Witness Counterexample: actual unparented top not root
-- statement:
--   No arbitrary lower marking is introduced: this uses the real rootComponent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L988-L1003
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L988-L1003

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

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actual_unparented_top_not_root (S : OddScale)
    (sigma : BDL26CanonicalHistoryMarks.Input S 2)
    (z : (state S 3).presentation.Z)
    (hp : parent S 3 (zVertex S 3 z) = none) :
    actualTopNode S (zVertex S 3 z) ∉
      BDL26CanonicalHistoryMarks.rootComponent S 2 sigma := by sorry
