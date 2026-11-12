-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_actual_base_Z_root_member
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actual_base_Z_root_member
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:44:19.037574+00:00
-- url     : https://prove2.me/theorems/ca39e1bf-4757-4a7c-a197-fc12461a369e
-- title:
--   BDL26 Canonical Root Witness Counterexample: actual base Z root member
-- statement:
--   The actual nonzero base mark reaches the original root.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L1500-L1519
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L1500-L1519

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

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actual_base_Z_root_member (S : OddScale)
    (sigma : BDL26CanonicalHistoryMarks.Input S 2)
    (hbase : BDL26CanonicalHistoryMarks.baseInput S 2 sigma = gamma2 S) :
    @Membership.mem.{0, 0} (BDL26CanonicalHistoryMarks.Node S 2)
      (Finset (BDL26CanonicalHistoryMarks.Node S 2))
      (@SetLike.instMembership.{0, 0} (Finset (BDL26CanonicalHistoryMarks.Node S 2))
        (BDL26CanonicalHistoryMarks.Node S 2)
        (@Finset.instSetLike.{0} (BDL26CanonicalHistoryMarks.Node S 2)))
      (BDL26CanonicalHistoryMarks.rootComponent S 2 sigma)
      (actualBaseNode S (zVertex S 1 (baseRetainedZ S))) := by sorry
