-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_sourceCochainContraction_mem_middleCocycleCode
-- name    : QEC.Coding.DistanceBalancing.sourceCochainContraction_mem_middleCocycleCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:18:49.937856+00:00
-- url     : https://prove2.me/theorems/b15d705c-1457-4c89-b6de-a5a809907b86
-- title:
--   Distance Balancing: source Cochain Contraction mem middle Cocycle Code
-- statement:
--   Contracting a product cocycle against a classical codeword produces a
--   source cocycle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L368-L414
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L368-L414

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

theorem QEC.Coding.DistanceBalancing.sourceCochainContraction_mem_middleCocycleCode
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hx : x ∈ (chainComplex D).middleCocycleCode.carrier)
    (c : Word (ZMod 2) classicalBit)
    (hc : Matrix.toLin' D.classicalBoundary c = 0) :
    sourceCochainContraction x c ∈
      (sourceChainComplex D).middleCocycleCode.carrier := by sorry
