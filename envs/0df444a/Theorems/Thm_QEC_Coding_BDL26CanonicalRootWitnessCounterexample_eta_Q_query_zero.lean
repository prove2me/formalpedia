-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_eta_Q_query_zero
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.eta_Q_query_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:07:12.840139+00:00
-- url     : https://prove2.me/theorems/d7264e14-0139-43ed-bcc9-6e790cbeb34e
-- title:
--   BDL26 Canonical Root Witness Counterexample: eta Q query zero
-- statement:
--   The BDL26 Canonical Root Witness Counterexample construction uses the eta Q query zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L1151-L1153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L1151-L1153

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

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.eta_Q_query_zero (S : OddScale) (q : (state S 2).presentation.Q) :
    restrictWordLinear ((LQ S).syndromeRegion q) (eta S) = 0 := by sorry
