-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_evenCombination_weight
-- name    : QEC.Distillation.Triorthogonal.BH12EvenFamily.evenCombination_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:44:38.520038+00:00
-- url     : https://prove2.me/theorems/164fe656-8ed8-417c-b710-bd4b586c98aa
-- title:
--   BH12 Even Family: even Combination weight
-- statement:
--   The BH12 Even Family construction uses the even Combination weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L782-L791
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L782-L791

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.Triorthogonal.BH12EvenFamily.evenCombination_weight (q : Nat) (i : Fin 8) :
    HammingWeight (evenCombination q (coefficientBits i)) =
      ![0, 4 + 4 * q, 4 + 4 * q, 4 + 4 * q, 8,
        4 + 4 * q, 4 + 4 * q, 4 + 4 * q] i := by sorry
