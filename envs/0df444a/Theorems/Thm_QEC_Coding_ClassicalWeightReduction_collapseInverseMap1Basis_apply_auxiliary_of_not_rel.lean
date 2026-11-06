-- Prove2me | Theorems.Thm_QEC_Coding_ClassicalWeightReduction_collapseInverseMap1Basis_apply_auxiliary_of_not_rel
-- name    : QEC.Coding.ClassicalWeightReduction.collapseInverseMap1Basis_apply_auxiliary_of_not_rel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:56:08.047345+00:00
-- url     : https://prove2.me/theorems/0c34e211-0bc2-4706-93e8-783f350fa2a0
-- title:
--   Classical Weight Reduction: collapse Inverse Map1 Basis apply auxiliary of not rel
-- statement:
--   The Classical Weight Reduction construction uses the collapse Inverse Map1 Basis apply auxiliary of not rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Distance.lean#L218-L242
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Distance.lean#L218-L242

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Collapse
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
set_option autoImplicit false
open QEC QEC.Coding
open scoped BigOperators
universe u v w
open QEC.Coding.ClassicalWeightReduction
variable {F Check Bit : Type u} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Check] [DecidableEq Check]
variable [Fintype Bit] [DecidableEq Bit]
variable (R : Check → Bit → Prop) [DecidableRel R]
omit [Fintype F] [DecidableEq F]

theorem QEC.Coding.ClassicalWeightReduction.collapseInverseMap1Basis_apply_auxiliary_of_not_rel
    (b : Bit) (a : AuxiliaryBit R) (hba : ¬R a.1 b) :
    collapseInverseMap1Basis (F := F) R b (Sum.inr a) = 0 := by sorry
