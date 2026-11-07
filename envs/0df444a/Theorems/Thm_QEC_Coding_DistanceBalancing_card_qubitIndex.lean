-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_card_qubitIndex
-- name    : QEC.Coding.DistanceBalancing.card_qubitIndex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:38:22.205343+00:00
-- url     : https://prove2.me/theorems/3cd46be4-8427-4e15-8946-4391122333d2
-- title:
--   Distance Balancing: card qubit Index
-- statement:
--   Exact physical-qubit count of the finite EKZ product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1451-L1455
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1451-L1455

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

theorem QEC.Coding.DistanceBalancing.card_qubitIndex :
    Fintype.card (QubitIndex xOne xTwo classicalBit classicalCheck) =
      Fintype.card xOne * Fintype.card classicalBit +
        Fintype.card xTwo * Fintype.card classicalCheck := by sorry
