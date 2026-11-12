-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_singleOddExtensionCode_weightSum
-- name    : QEC.Distillation.Triorthogonal.BH12EvenFamily.singleOddExtensionCode_weightSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:44:40.831509+00:00
-- url     : https://prove2.me/theorems/23044e63-7f8a-4d88-bcb7-ed172567a5d3
-- title:
--   BH12 Even Family: single Odd Extension Code weight Sum
-- statement:
--   The BH12 Even Family construction uses the single Odd Extension Code weight Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L1135-L1159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L1135-L1159

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
set_option maxHeartbeats 800000

theorem QEC.Distillation.Triorthogonal.BH12EvenFamily.singleOddExtensionCode_weightSum {A : Type*} [AddCommMonoid A]
    {q : Nat} (a : OddRow q) (f : Nat → A) :
    codeWeightSum (singleOddExtensionCode a) f =
      (f 0 + f 8 + 6 • f (4 + 4 * q)) +
        (2 • f 7 + 6 • f (3 + 4 * q)) := by sorry
