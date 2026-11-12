-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_localW_at_q2_imbalance
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.localW_at_q2_imbalance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:07:41.362076+00:00
-- url     : https://prove2.me/theorems/f65d89df-92e4-43db-adce-90dbbe9400a1
-- title:
--   BDL26 Canonical Root Witness Counterexample: local W at q2 imbalance
-- statement:
--   The BDL26 Canonical Root Witness Counterexample construction uses the local W at q2 imbalance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L592-L599
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L592-L599

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

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.localW_at_q2_imbalance (S : OddScale) :
    localW S (q2 S) (terminalVertex S (q2 S) (r2 S) (q2_incidence S) 0) +
      localW S (q2 S) (terminalVertex S (q2 S) (r2 S) (q2_incidence S) 1) = 1 := by sorry
