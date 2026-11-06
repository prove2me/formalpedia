-- Prove2me | Theorems.Thm_QEC_Coding_ClassicalWeightReduction_single_checkIncidenceAt_apply
-- name    : QEC.Coding.ClassicalWeightReduction.single_checkIncidenceAt_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:09:07.933457+00:00
-- url     : https://prove2.me/theorems/6b2e237e-cd35-41ff-bbf7-0a4bb21530b1
-- title:
--   Classical Weight Reduction: single check Incidence At apply
-- statement:
--   The Classical Weight Reduction construction uses the single check Incidence At apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L322-L341
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L322-L341

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

theorem QEC.Coding.ClassicalWeightReduction.single_checkIncidenceAt_apply (e : Incidence R)
    (k : Fin (Fintype.card (CheckNeighbor R e.1.1))) :
    (Pi.single (Sum.inl (checkIncidenceAt R e.1.1 k)) 1 :
        Word F (WeightReducedCheck R)) (Sum.inl e) =
      (Pi.single k 1 : Word F
        (Fin (Fintype.card (CheckNeighbor R e.1.1)))) (checkPosition R e) := by sorry
