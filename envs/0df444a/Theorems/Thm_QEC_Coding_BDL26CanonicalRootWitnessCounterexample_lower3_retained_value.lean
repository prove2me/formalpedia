-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_lower3_retained_value
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.lower3_retained_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:13:26.385205+00:00
-- url     : https://prove2.me/theorems/6dc7cbb9-efba-423c-8942-8fca04a15064
-- title:
--   BDL26 Canonical Root Witness Counterexample: lower3 retained value
-- statement:
--   The BDL26 Canonical Root Witness Counterexample construction uses the lower3 retained value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L809-L824
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L809-L824

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

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.lower3_retained_value (S : OddScale) (b : Fin 2) :
    (lower3 S).val ((A S).induced.zPairEquiv (r2 S,b)).val =
      1 + localW S (q2 S) (terminalVertex S (q2 S) (r2 S) (q2_incidence S) b) := by sorry
