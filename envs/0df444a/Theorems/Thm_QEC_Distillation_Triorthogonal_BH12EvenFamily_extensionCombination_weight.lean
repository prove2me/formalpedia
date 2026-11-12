-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_extensionCombination_weight
-- name    : QEC.Distillation.Triorthogonal.BH12EvenFamily.extensionCombination_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:39:14.565444+00:00
-- url     : https://prove2.me/theorems/0579dc23-426f-40fd-9af1-d2a043210b10
-- title:
--   BH12 Even Family: extension Combination weight
-- statement:
--   The BH12 Even Family construction uses the extension Combination weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L1051-L1073
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L1051-L1073

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.Triorthogonal.BH12EvenFamily.extensionCombination_weight {q : Nat} (a : OddRow q)
    (b : ZMod 2) (i : Fin 8) :
    HammingWeight (extensionCombination a (extensionCoefficientBits (b, i))) =
      if b = 0 then
        ![0, 4 + 4 * q, 4 + 4 * q, 4 + 4 * q, 8,
          4 + 4 * q, 4 + 4 * q, 4 + 4 * q] i
      else
        ![7, 3 + 4 * q, 3 + 4 * q, 3 + 4 * q, 7,
          3 + 4 * q, 3 + 4 * q, 3 + 4 * q] i := by sorry
