-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_no_actual_top_Z_marked_neighbor
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.no_actual_top_Z_marked_neighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:14:33.722441+00:00
-- url     : https://prove2.me/theorems/0aa49444-c5e1-411e-8f14-a7bcedb53785
-- title:
--   BDL26 Canonical Root Witness Counterexample: no actual top Z marked neighbor
-- statement:
--   The compiled generic isolation lemma on the same typed literal Sigma nodes.
--   No concrete graph record or recursive presentation is unfolded here.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L959-L972
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L959-L972

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

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.no_actual_top_Z_marked_neighbor (S : OddScale)
    (sigma : BDL26CanonicalHistoryMarks.Input S 2)
    (z : (state S 3).presentation.Z)
    (hparent : parent S 3 (zVertex S 3 z) = none)
    (w : BDL26CanonicalHistoryMarks.Node S 2)
    (hw : w ∈ BDL26CanonicalHistoryMarks.marks S 2 sigma) :
    ¬ (decodingGraph S 4).adjacent (actualTopNode S (zVertex S 3 z)) w := by sorry
