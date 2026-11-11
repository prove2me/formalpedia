-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_rootMask_Q_coordinate_owner
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.rootMask_Q_coordinate_owner
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:09:33.999328+00:00
-- url     : https://prove2.me/theorems/bfcc34ab-e4f1-48ae-9cc3-f0231159433f
-- title:
--   BDL26 Canonical Root Witness Counterexample: root Mask Q coordinate owner
-- statement:
--   The BDL26 Canonical Root Witness Counterexample construction uses the root Mask Q coordinate owner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L1889-L1896
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L1889-L1896

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

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.rootMask_Q_coordinate_owner (S : OddScale)
    (p : LocalRegionIndex ((LQ S).syndromeRegion (q2 S))) :
    BDL26CanonicalHistoryMarks.syndromeOwner S 2 (0 : StepIndex 2) p.val =
      @Vertex.q (state S 2).presentation (q2 S) := by sorry
