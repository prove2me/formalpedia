-- Prove2me | Theorems.Thm_QEC_Coding_ClassicalWeightReduction_collapseHomotopy0_apply_original
-- name    : QEC.Coding.ClassicalWeightReduction.collapseHomotopy0_apply_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:56:36.589679+00:00
-- url     : https://prove2.me/theorems/f2365cfd-bcd7-45eb-af04-401d8296ba2d
-- title:
--   Classical Weight Reduction: collapse Homotopy0 apply original
-- statement:
--   The Classical Weight Reduction construction uses the collapse Homotopy0 apply original property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Distance.lean#L189-L199
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Distance.lean#L189-L199

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

theorem QEC.Coding.ClassicalWeightReduction.collapseHomotopy0_apply_original
    (x : Word F (BitSplitCheck R)) (b : Bit) :
    collapseHomotopy0 (F := F) R x (Sum.inl b) = 0 := by sorry
