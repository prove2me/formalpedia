-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_lower3_X_query_zero
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.lower3_X_query_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:10:44.641893+00:00
-- url     : https://prove2.me/theorems/cfc0a4b5-ad46-4d73-8942-e3df73307538
-- title:
--   BDL26 Canonical Root Witness Counterexample: lower3 X query zero
-- statement:
--   The BDL26 Canonical Root Witness Counterexample construction uses the lower3 X query zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L710-L714
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L710-L714

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

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.lower3_X_query_zero (S : OddScale) (x : (state S 2).presentation.X) :
    restrictWordLinear ((LX S).syndromeRegion x) (lower3 S).val = 0 := by sorry
