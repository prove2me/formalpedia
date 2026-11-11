-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_selected_top_map2_apply
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.selected_top_map2_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:02:57.195043+00:00
-- url     : https://prove2.me/theorems/fa5e5a48-e193-422b-a58d-36d0015aca65
-- title:
--   BDL26 Canonical Root Witness Counterexample: selected top map2 apply
-- statement:
--   The single actual top RZ coordinate chart, normalized before rewriting.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L1050-L1056
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L1050-L1056

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

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.selected_top_map2_apply (S : OddScale) (word : Word3 S)
    (z : (state S 3).presentation.Z) (v : ZDoubleCylinderVertex (state S 3).presentation z S) :
    ((indexedDecoderData S 4).selectedMap (3 : StepIndex 4)).map2 word ⟨z,v⟩ =
      if v = rzMap1ZRoot (state S 3).presentation (state S 3).admissible z S
      then word z else 0 := by sorry
