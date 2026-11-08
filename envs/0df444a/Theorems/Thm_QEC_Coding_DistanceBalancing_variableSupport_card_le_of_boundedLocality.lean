-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_variableSupport_card_le_of_boundedLocality
-- name    : QEC.Coding.DistanceBalancing.variableSupport_card_le_of_boundedLocality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:22:20.10509+00:00
-- url     : https://prove2.me/theorems/c6568d9d-065f-4d8d-a3bf-9e1449ff98df
-- title:
--   Distance Balancing: variable Support card le of bounded Locality
-- statement:
--   The Distance Balancing construction uses the variable Support card le of bounded Locality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Locality.lean#L418-L427
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Locality.lean#L418-L427

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.DistanceBalancing
universe u
open QEC.Coding.FiberBundle
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable (D : Data xZero xOne xTwo classicalBit classicalCheck)

theorem QEC.Coding.DistanceBalancing.variableSupport_card_le_of_boundedLocality
    {check var : Type u} [Fintype check] [Fintype var]
    (I : QEC.QLDPC.CheckIncidence check var) {B : Nat}
    (h : BoundedLocality I.localityProfile B) (q : var) :
    (I.variableSupport q).card ≤ B := by sorry
