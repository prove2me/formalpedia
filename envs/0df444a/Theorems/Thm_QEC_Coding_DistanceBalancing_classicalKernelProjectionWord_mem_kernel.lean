-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_classicalKernelProjectionWord_mem_kernel
-- name    : QEC.Coding.DistanceBalancing.classicalKernelProjectionWord_mem_kernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:19:04.908515+00:00
-- url     : https://prove2.me/theorems/a24978b5-5aa5-4b3c-8f8e-0a8082f579d0
-- title:
--   Distance Balancing: classical Kernel Projection Word mem kernel
-- statement:
--   The Distance Balancing construction uses the classical Kernel Projection Word mem kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L466-L484
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L466-L484

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

theorem QEC.Coding.DistanceBalancing.classicalKernelProjectionWord_mem_kernel
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    (a : classicalBit) :
    Matrix.toLin' D.classicalBoundary
      (classicalKernelProjectionWord D S a) = 0 := by sorry
