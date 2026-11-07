-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_mem_firstCoboundaryCheckCode_of_projected_slices
-- name    : QEC.Coding.DistanceBalancing.mem_firstCoboundaryCheckCode_of_projected_slices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:19:47.53539+00:00
-- url     : https://prove2.me/theorems/843ca05c-ed2b-4332-a002-78bd2abc1f96
-- title:
--   Distance Balancing: mem first Coboundary Check Code of projected slices
-- statement:
--   The Distance Balancing construction uses the mem first Coboundary Check Code of projected slices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L768-L780
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L768-L780

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

theorem QEC.Coding.DistanceBalancing.mem_firstCoboundaryCheckCode_of_projected_slices
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hx : x ∈ (chainComplex D).middleCocycleCode.carrier)
    (hFill : ∀ a : classicalBit,
      projectedSourceCochain D S x a ∈
        (sourceChainComplex D).firstCoboundaryCheckCode.carrier) :
    x ∈ (chainComplex D).firstCoboundaryCheckCode.carrier := by sorry
