-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_oddCosetWord_weight
-- name    : QEC.Distillation.Triorthogonal.BH12EvenFamily.oddCosetWord_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:44:32.622352+00:00
-- url     : https://prove2.me/theorems/73d80388-ae8a-4a60-879e-a25cf6fb9a4d
-- title:
--   BH12 Even Family: odd Coset Word weight
-- statement:
--   The BH12 Even Family construction uses the odd Coset Word weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L855-L867
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L855-L867

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.Triorthogonal.BH12EvenFamily.oddCosetWord_weight {q : Nat} (a : OddRow q) (i : Fin 8) :
    HammingWeight (oddCosetWord a i) =
      ![7, 3 + 4 * q, 3 + 4 * q, 3 + 4 * q, 7,
        3 + 4 * q, 3 + 4 * q, 3 + 4 * q] i := by sorry
