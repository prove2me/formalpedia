-- Prove2me | Theorems.Thm_QEC_Coding_ClassicalWeightReduction_optionalSingle_map_auxiliaryBitIndex_apply_of_ne
-- name    : QEC.Coding.ClassicalWeightReduction.optionalSingle_map_auxiliaryBitIndex_apply_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:08:55.228863+00:00
-- url     : https://prove2.me/theorems/c9d08996-2998-46a2-a8c5-7336eb6af10f
-- title:
--   Classical Weight Reduction: optional Single map auxiliary Bit Index apply of ne
-- statement:
--   The Classical Weight Reduction construction uses the optional Single map auxiliary Bit Index apply of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L278-L284
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L278-L284

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
omit [Fintype F] [DecidableEq F] [Fintype Check]

theorem QEC.Coding.ClassicalWeightReduction.optionalSingle_map_auxiliaryBitIndex_apply_of_ne
    {c c' : Check} (hc : c ≠ c')
    (o : Option (Fin (Fintype.card (CheckNeighbor R c) - 1)))
    (j : Fin (Fintype.card (CheckNeighbor R c') - 1)) :
    optionalSingle (F := F) (o.map (auxiliaryBitIndex R c))
        (Sum.inr ⟨c', j⟩) = 0 := by sorry
