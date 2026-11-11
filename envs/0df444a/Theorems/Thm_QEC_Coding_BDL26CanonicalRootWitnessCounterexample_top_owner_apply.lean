-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_top_owner_apply
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.top_owner_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:06:31.49464+00:00
-- url     : https://prove2.me/theorems/b7853925-5b19-4c4e-b051-79f57b0b574b
-- title:
--   BDL26 Canonical Root Witness Counterexample: top owner apply
-- statement:
--   Typed actual top RZ owner, isolated from root-mask simplification.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L1041-L1044
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L1041-L1044

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

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.top_owner_apply (S : OddScale) (z : (state S 3).presentation.Z)
    (v : ZDoubleCylinderVertex (state S 3).presentation z S) :
    BDL26CanonicalHistoryMarks.syndromeOwner S 2 (1 : StepIndex 2)
      (⟨z,v⟩ : FamilyZ S 4 level4) = zVertex S 3 z := by sorry
