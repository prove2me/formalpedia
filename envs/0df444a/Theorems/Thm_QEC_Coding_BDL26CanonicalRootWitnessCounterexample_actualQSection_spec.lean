-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_actualQSection_spec
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actualQSection_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:00:03.877518+00:00
-- url     : https://prove2.me/theorems/cd138359-319b-4f98-ae30-01014f7e7979
-- title:
--   BDL26 Canonical Root Witness Counterexample: actual QSection spec
-- statement:
--   The BDL26 Canonical Root Witness Counterexample construction uses the actual QSection spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L394-L400
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L394-L400

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

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actualQSection_spec (S : OddScale) (q : (state S 2).presentation.Q)
    (t : LocalQSyndrome S q)
    (ht : t ∈ LinearMap.range ((A S).contract.rx_local_complexes.cqDelta1 q)) :
    (A S).contract.rx_local_complexes.cqDelta1 q (actualQSection S q t ht) = t ∧
      HammingWeight ((A S).contract.support_decomposition.cqFlow q
        (actualQSection S q t ht)) ≤ HammingWeight t := by sorry
