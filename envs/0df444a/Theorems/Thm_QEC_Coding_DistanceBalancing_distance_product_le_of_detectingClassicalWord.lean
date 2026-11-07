-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_distance_product_le_of_detectingClassicalWord
-- name    : QEC.Coding.DistanceBalancing.distance_product_le_of_detectingClassicalWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:21:09.780173+00:00
-- url     : https://prove2.me/theorems/9861b930-2e67-455b-a4a3-16f0b2f80fa9
-- title:
--   Distance Balancing: distance product le of detecting Classical Word
-- statement:
--   The Distance Balancing construction uses the distance product le of detecting Classical Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1347-L1365
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1347-L1365

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.DistanceBalancing
universe u
open scoped BigOperators
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable (D : Data xZero xOne xTwo classicalBit classicalCheck)

theorem QEC.Coding.DistanceBalancing.distance_product_le_of_detectingClassicalWord
    {dSource dClassical total : Nat}
    (hClassical : ClassicalDistanceAtLeast
      D.classicalBoundary dClassical)
    (w : Word (ZMod 2) classicalBit)
    (hwKernel : Matrix.toLin' D.classicalBoundary w = 0)
    (hwNonzero : w ≠ 0)
    (hwBound : dSource * HammingWeight w ≤ total) :
    dClassical * dSource ≤ total := by sorry
