-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_actual_top_Z_marked
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actual_top_Z_marked
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:08:25.681844+00:00
-- url     : https://prove2.me/theorems/5fa27da7-25a3-4e8a-a7f1-13c8b8af50ea
-- title:
--   BDL26 Canonical Root Witness Counterexample: actual top Z marked
-- statement:
--   A nonzero genuine top coordinate marks its actual Z-cylinder owner.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L1665-L1707
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L1665-L1707

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

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actual_top_Z_marked (S : OddScale)
    (sigma : BDL26CanonicalHistoryMarks.Input S 2)
    (z : (state S 3).presentation.Z)
    (v : ZDoubleCylinderVertex (state S 3).presentation z S)
    (hp : sigma.val (⟨z,v⟩ : FamilyZ S 4 level4) ≠ 0) :
    actualTopNode S (zVertex S 3 z) ∈ BDL26CanonicalHistoryMarks.marks S 2 sigma := by sorry
