-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_HammingWeight_eq_sum_indicator
-- name    : QEC.Coding.DistanceBalancing.HammingWeight_eq_sum_indicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:17:21.569429+00:00
-- url     : https://prove2.me/theorems/fafce5f5-0820-43e6-b57e-2bc246de7827
-- title:
--   Distance Balancing: Hamming Weight eq sum indicator
-- statement:
--   Hamming weight is the sum of its nonzero-coordinate indicators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L924-L928
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L924-L928

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

theorem QEC.Coding.DistanceBalancing.HammingWeight_eq_sum_indicator
    {i : Type u} [Fintype i] (w : Word (ZMod 2) i) :
    HammingWeight w = ∑ j : i, if w j ≠ 0 then 1 else 0 := by sorry
