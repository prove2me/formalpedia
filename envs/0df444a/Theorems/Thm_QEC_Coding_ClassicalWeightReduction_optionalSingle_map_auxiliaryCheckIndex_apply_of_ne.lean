-- Prove2me | Theorems.Thm_QEC_Coding_ClassicalWeightReduction_optionalSingle_map_auxiliaryCheckIndex_apply_of_ne
-- name    : QEC.Coding.ClassicalWeightReduction.optionalSingle_map_auxiliaryCheckIndex_apply_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:08:54.256589+00:00
-- url     : https://prove2.me/theorems/9a38ec0d-6534-4e23-8bb5-02ae52536338
-- title:
--   Classical Weight Reduction: optional Single map auxiliary Check Index apply of ne
-- statement:
--   The Classical Weight Reduction construction uses the optional Single map auxiliary Check Index apply of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L250-L256
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L250-L256

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
omit [Fintype F] [DecidableEq F] [Fintype Bit]

theorem QEC.Coding.ClassicalWeightReduction.optionalSingle_map_auxiliaryCheckIndex_apply_of_ne
    {b b' : Bit} (hb : b ≠ b')
    (o : Option (Fin (Fintype.card (BitNeighbor R b) - 1)))
    (j : Fin (Fintype.card (BitNeighbor R b') - 1)) :
    optionalSingle (F := F) (o.map (auxiliaryCheckIndex R b))
        (Sum.inr ⟨b', j⟩) = 0 := by sorry
