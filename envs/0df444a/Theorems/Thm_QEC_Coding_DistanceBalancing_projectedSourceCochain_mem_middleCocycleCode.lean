-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_projectedSourceCochain_mem_middleCocycleCode
-- name    : QEC.Coding.DistanceBalancing.projectedSourceCochain_mem_middleCocycleCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:19:29.929442+00:00
-- url     : https://prove2.me/theorems/7f474ce5-66fe-4563-8830-0222dc81ebaf
-- title:
--   Distance Balancing: projected Source Cochain mem middle Cocycle Code
-- statement:
--   The Distance Balancing construction uses the projected Source Cochain mem middle Cocycle Code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L558-L569
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L558-L569

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

theorem QEC.Coding.DistanceBalancing.projectedSourceCochain_mem_middleCocycleCode
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hx : x ∈ (chainComplex D).middleCocycleCode.carrier)
    (a : classicalBit) :
    projectedSourceCochain D S x a ∈
      (sourceChainComplex D).middleCocycleCode.carrier := by sorry
