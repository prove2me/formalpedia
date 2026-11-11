-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_error_coboundary_zero_on_readRegion
-- name    : QEC.Coding.BDL26RXInfluenceBounds.error_coboundary_zero_on_readRegion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:47:03.057009+00:00
-- url     : https://prove2.me/theorems/337e9447-798f-4b05-a4c3-be87c243e27f
-- title:
--   BDL26 RXInfluence Bounds: error coboundary zero on read Region
-- statement:
--   Every term of the actual error coboundary vanishes on an unread region.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L201-L219
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L201-L219

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

theorem QEC.Coding.BDL26RXInfluenceBounds.error_coboundary_zero_on_readRegion (e : (indexedFamily S depth).Cochain1 i.succ)
    (z : FamilyZ S depth i.castSucc) (hz : z ∉ errorInfluence S depth i h e)
    (p : FamilyZ S depth i.succ) (hp : p ∈ readRegion S depth i h z) :
    (indexedFamily S depth).coboundary1 i.succ e p = 0 := by sorry
