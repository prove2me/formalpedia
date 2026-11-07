-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_sum_classicalBoundary_smul_sourceHomologySlice_eq_zero
-- name    : QEC.Coding.DistanceBalancing.sum_classicalBoundary_smul_sourceHomologySlice_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:19:57.057406+00:00
-- url     : https://prove2.me/theorems/34856b1b-f23d-408e-945a-6f01a265312a
-- title:
--   Distance Balancing: sum classical Boundary smul source Homology Slice eq zero
-- statement:
--   The classical parity-check equations hold with values in source
--   homology.  This is the Künneth slice relation used for the multiplicative
--   distance bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L842-L879
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L842-L879

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

theorem QEC.Coding.DistanceBalancing.sum_classicalBoundary_smul_sourceHomologySlice_eq_zero
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (b : classicalCheck) :
    (∑ a : classicalBit,
      D.classicalBoundary b a • sourceHomologySlice D z hz a) = 0 := by sorry
