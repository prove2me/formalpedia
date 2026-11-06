-- Prove2me | Theorems.Thm_QEC_Coding_ClassicalWeightReduction_single_bitIncidenceAt_apply_of_ne
-- name    : QEC.Coding.ClassicalWeightReduction.single_bitIncidenceAt_apply_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:09:02.76783+00:00
-- url     : https://prove2.me/theorems/bd0e6b6b-b43a-49d8-97f9-5932d33a7267
-- title:
--   Classical Weight Reduction: single bit Incidence At apply of ne
-- statement:
--   The Classical Weight Reduction construction uses the single bit Incidence At apply of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L309-L319
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L309-L319

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

theorem QEC.Coding.ClassicalWeightReduction.single_bitIncidenceAt_apply_of_ne {b : Bit} (e : Incidence R)
    (hb : e.1.2 ≠ b) (k : Fin (Fintype.card (BitNeighbor R b))) :
    (Pi.single (Sum.inl (bitIncidenceAt R b k)) 1 :
        Word F (WeightReducedBit R)) (Sum.inl e) = 0 := by sorry
