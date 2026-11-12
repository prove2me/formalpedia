-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_oddCosetCoefficient_weightSum
-- name    : QEC.Distillation.Triorthogonal.BH12EvenFamily.oddCosetCoefficient_weightSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:44:54.837103+00:00
-- url     : https://prove2.me/theorems/fb9920c6-ffd3-4176-9491-e7855e68ae5e
-- title:
--   BH12 Even Family: odd Coset Coefficient weight Sum
-- statement:
--   The BH12 Even Family construction uses the odd Coset Coefficient weight Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L877-L883
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L877-L883

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.Triorthogonal.BH12EvenFamily.oddCosetCoefficient_weightSum {A : Type*} [AddCommMonoid A]
    {q : Nat} (a : OddRow q) (f : Nat → A) :
    (∑ i : Fin 8, f (HammingWeight (oddCosetWord a i))) =
      2 • f 7 + 6 • f (3 + 4 * q) := by sorry
