-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_extensionCoefficient_weightSum
-- name    : QEC.Distillation.Triorthogonal.BH12EvenFamily.extensionCoefficient_weightSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:07:47.387057+00:00
-- url     : https://prove2.me/theorems/50742ba9-7f20-4b92-b918-dab5349a87ad
-- title:
--   BH12 Even Family: extension Coefficient weight Sum
-- statement:
--   The BH12 Even Family construction uses the extension Coefficient weight Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L1075-L1096
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L1075-L1096

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.Triorthogonal.BH12EvenFamily.extensionCoefficient_weightSum {A : Type*} [AddCommMonoid A]
    {q : Nat} (a : OddRow q) (f : Nat → A) :
    (∑ bi : ZMod 2 × Fin 8,
      f (HammingWeight
        (extensionCombination a (extensionCoefficientBits bi)))) =
      (f 0 + f 8 + 6 • f (4 + 4 * q)) +
        (2 • f 7 + 6 • f (3 + 4 * q)) := by sorry
