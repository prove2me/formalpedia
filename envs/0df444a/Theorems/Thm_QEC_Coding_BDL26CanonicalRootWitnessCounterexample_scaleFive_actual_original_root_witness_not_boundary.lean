-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_scaleFive_actual_original_root_witness_not_boundary
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.scaleFive_actual_original_root_witness_not_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:46:44.193319+00:00
-- url     : https://prove2.me/theorems/82d43d0c-919b-41a7-ac24-fc9fcba9f15e
-- title:
--   BDL26 Canonical Root Witness Counterexample: scale Five actual original root witness not boundary
-- statement:
--   Explicit concrete instance requested before the uniform strengthening.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L1814-L1819
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L1814-L1819

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

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.scaleFive_actual_original_root_witness_not_boundary :
    ∃ sigma : (indexedFamily scaleFive 4).Syndrome (4 : LevelIndex 4),
      (BDL26CanonicalHistoryMarks.baseInput scaleFive 2 sigma).val ≠ 0 ∧
      topWitness scaleFive sigma ∉
        LinearMap.range ((indexedFamily scaleFive 4).coboundary1 (4 : LevelIndex 4)) := by sorry
