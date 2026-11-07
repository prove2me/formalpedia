-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_projectedSourceCochain_eq
-- name    : QEC.Coding.DistanceBalancing.projectedSourceCochain_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:19:34.390194+00:00
-- url     : https://prove2.me/theorems/f62e3a2c-e3fc-4c22-83a8-7cac2741580c
-- title:
--   Distance Balancing: projected Source Cochain eq
-- statement:
--   The Distance Balancing construction uses the projected Source Cochain eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L544-L556
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L544-L556

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

theorem QEC.Coding.DistanceBalancing.projectedSourceCochain_eq
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (a : classicalBit) :
    projectedSourceCochain D S x a =
      xOneBitSlice x a +
        ∑ b : classicalCheck,
          D.classicalBoundary b a • sourceCochainLift S x b := by sorry
