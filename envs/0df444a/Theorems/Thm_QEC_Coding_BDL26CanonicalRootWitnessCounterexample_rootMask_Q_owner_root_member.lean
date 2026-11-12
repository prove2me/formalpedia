-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_rootMask_Q_owner_root_member
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.rootMask_Q_owner_root_member
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:49:08.223604+00:00
-- url     : https://prove2.me/theorems/8db8833e-ef36-43ce-bc60-b49c9ab5129e
-- title:
--   BDL26 Canonical Root Witness Counterexample: root Mask Q owner root member
-- statement:
--   A genuine horizontal incidence joins the marked Q owner to the rooted Z owner.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L1920-L1933
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L1920-L1933

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

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.rootMask_Q_owner_root_member (S : OddScale) :
    actualMidNode S (@Vertex.q (state S 2).presentation (q2 S)) ∈
      BDL26CanonicalHistoryMarks.rootComponent S 2 (upper4 S) := by sorry
