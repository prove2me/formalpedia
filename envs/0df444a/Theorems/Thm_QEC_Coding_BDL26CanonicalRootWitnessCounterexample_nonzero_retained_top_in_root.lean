-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_nonzero_retained_top_in_root
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.nonzero_retained_top_in_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:46:24.371617+00:00
-- url     : https://prove2.me/theorems/2fbc6359-0376-4701-8043-8516f03238f2
-- title:
--   BDL26 Canonical Root Witness Counterexample: nonzero retained top in root
-- statement:
--   Nonzero retained input marks the actual top node, whose original parent
--   is the already-rooted lower Z node. Closed top corrections do not affect it.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L1739-L1757
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L1739-L1757

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

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.nonzero_retained_top_in_root (S : OddScale) (b : Fin 2)
    (hb : (lower3 S).val ((A S).induced.zPairEquiv (r2 S,b)).val ≠ 0) :
    @Membership.mem.{0, 0} (BDL26CanonicalHistoryMarks.Node S 2)
      (Finset (BDL26CanonicalHistoryMarks.Node S 2))
      (@SetLike.instMembership.{0, 0} (Finset (BDL26CanonicalHistoryMarks.Node S 2))
        (BDL26CanonicalHistoryMarks.Node S 2)
        (@Finset.instSetLike.{0} (BDL26CanonicalHistoryMarks.Node S 2)))
      (BDL26CanonicalHistoryMarks.rootComponent S 2 (upper4 S))
      (actualTopNode S (zVertex S 3 ((A S).induced.zPairEquiv (r2 S,b)).val)) := by sorry
