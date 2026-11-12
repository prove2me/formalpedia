-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_evenCode_weightEnumerator
-- name    : QEC.Distillation.Triorthogonal.BH12EvenFamily.evenCode_weightEnumerator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:39:37.982587+00:00
-- url     : https://prove2.me/theorems/98262549-45c9-4198-b7a2-4a5884a780f1
-- title:
--   BH12 Even Family: even Code weight Enumerator
-- statement:
--   The source formula `W_G₀(x) = 1 + x⁸ + 6x^(4+2k)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L1171-L1180
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L1171-L1180

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.Triorthogonal.BH12EvenFamily.evenCode_weightEnumerator (q : Nat) :
    codeWeightEnumerator (family q).evenCode =
      1 + Polynomial.X ^ 8 + 6 * Polynomial.X ^ (4 + 2 * logicalCount q) := by sorry
