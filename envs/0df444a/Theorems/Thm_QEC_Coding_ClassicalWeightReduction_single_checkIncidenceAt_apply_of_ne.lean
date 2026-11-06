-- Prove2me | Theorems.Thm_QEC_Coding_ClassicalWeightReduction_single_checkIncidenceAt_apply_of_ne
-- name    : QEC.Coding.ClassicalWeightReduction.single_checkIncidenceAt_apply_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:09:09.059781+00:00
-- url     : https://prove2.me/theorems/b7c85311-6cc1-4e84-99bf-7e2e2a52500f
-- title:
--   Classical Weight Reduction: single check Incidence At apply of ne
-- statement:
--   The Classical Weight Reduction construction uses the single check Incidence At apply of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L344-L354
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L344-L354

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Core
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ClassicalWeightReduction
open scoped BigOperators
universe u v w
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {Check : Type v} {Bit : Type w}
variable [Fintype Check] [DecidableEq Check]
variable [Fintype Bit] [DecidableEq Bit]
variable (R : Check → Bit → Prop) [DecidableRel R]
omit [Fintype F] [DecidableEq F]

theorem QEC.Coding.ClassicalWeightReduction.single_checkIncidenceAt_apply_of_ne {c : Check} (e : Incidence R)
    (hc : e.1.1 ≠ c) (k : Fin (Fintype.card (CheckNeighbor R c))) :
    (Pi.single (Sum.inl (checkIncidenceAt R c k)) 1 :
        Word F (WeightReducedCheck R)) (Sum.inl e) = 0 := by sorry
