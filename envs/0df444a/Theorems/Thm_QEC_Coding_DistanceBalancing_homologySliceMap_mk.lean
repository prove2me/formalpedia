-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_homologySliceMap_mk
-- name    : QEC.Coding.DistanceBalancing.homologySliceMap_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:21:37.699502+00:00
-- url     : https://prove2.me/theorems/3f0b10a3-9ad3-4460-85cf-2a3ea2a0b551
-- title:
--   Distance Balancing: homology Slice Map mk
-- statement:
--   The Distance Balancing construction uses the homology Slice Map mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Dimension.lean#L254-L259
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Dimension.lean#L254-L259

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Dimension
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.DistanceBalancing
universe u
open scoped TensorProduct
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable (D : Data xZero xOne xTwo classicalBit classicalCheck)

theorem QEC.Coding.DistanceBalancing.homologySliceMap_mk
    (z : (chainComplex D).middleCycleCode.carrier) :
    homologySliceMap D
        ((chainComplex D).middleBoundaryInCycles.mkQ z) =
      cycleToHomologySlices D z := by sorry

attribute [defeq] QEC.Coding.DistanceBalancing.homologySliceMap_mk
