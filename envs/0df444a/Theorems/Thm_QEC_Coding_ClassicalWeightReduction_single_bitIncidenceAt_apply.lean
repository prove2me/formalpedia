-- Prove2me | Theorems.Thm_QEC_Coding_ClassicalWeightReduction_single_bitIncidenceAt_apply
-- name    : QEC.Coding.ClassicalWeightReduction.single_bitIncidenceAt_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:09:50.478807+00:00
-- url     : https://prove2.me/theorems/f6b16866-93fe-45ba-a23e-a26fb3831a82
-- title:
--   Classical Weight Reduction: single bit Incidence At apply
-- statement:
--   The Classical Weight Reduction construction uses the single bit Incidence At apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L287-L306
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L287-L306

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

theorem QEC.Coding.ClassicalWeightReduction.single_bitIncidenceAt_apply (e : Incidence R)
    (k : Fin (Fintype.card (BitNeighbor R e.1.2))) :
    (Pi.single (Sum.inl (bitIncidenceAt R e.1.2 k)) 1 :
        Word F (WeightReducedBit R)) (Sum.inl e) =
      (Pi.single k 1 : Word F
        (Fin (Fintype.card (BitNeighbor R e.1.2)))) (bitPosition R e) := by sorry
