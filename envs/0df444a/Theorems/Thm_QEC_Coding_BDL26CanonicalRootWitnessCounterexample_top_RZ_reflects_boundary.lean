-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_top_RZ_reflects_boundary
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.top_RZ_reflects_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:14:02.244435+00:00
-- url     : https://prove2.me/theorems/fc90cae2-c57f-426c-94a9-91260cb3d945
-- title:
--   BDL26 Canonical Root Witness Counterexample: top RZ reflects boundary
-- statement:
--   The selected RZ map reflects the actual coboundary range, on arbitrary words.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L847-L863
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L847-L863

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

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.top_RZ_reflects_boundary (S : OddScale) (eta : Word3 S)
    (h : ((indexedDecoderData S 4).selectedMap (3 : StepIndex 4)).map2 eta ∈
      LinearMap.range ((CF S).coboundary1 level4)) :
    eta ∈ LinearMap.range (d3 S) := by sorry
