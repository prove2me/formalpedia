-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_basisSyndrome_weight_le_four
-- name    : QEC.Coding.BDL26RXInfluenceBounds.basisSyndrome_weight_le_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:00:01.440539+00:00
-- url     : https://prove2.me/theorems/dc9505be-35ee-4824-9dbd-8dc111f38c9d
-- title:
--   BDL26 RXInfluence Bounds: basis Syndrome weight le four
-- statement:
--   The literal upper basis coboundary has at most four incident Z coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L156-L160
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L156-L160

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXInfluenceBounds
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter BDL26RXCoarseInfluence BDL26BoundedValence
open BDL26GraphQuantitativeBounds BDL26RZMap1CoordinateBridge
open MultiscaleDecoder RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2 = 0)

theorem QEC.Coding.BDL26RXInfluenceBounds.basisSyndrome_weight_le_four (q : FamilyQ S depth i.succ) :
    HammingWeight (basisSyndrome S depth i q) ≤ 4 := by sorry
