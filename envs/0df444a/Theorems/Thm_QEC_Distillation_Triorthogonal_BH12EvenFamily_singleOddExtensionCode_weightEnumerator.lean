-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_singleOddExtensionCode_weightEnumerator
-- name    : QEC.Distillation.Triorthogonal.BH12EvenFamily.singleOddExtensionCode_weightEnumerator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:40:58.332883+00:00
-- url     : https://prove2.me/theorems/e070ac59-8dc5-48f4-9f4b-93daf14d127b
-- title:
--   BH12 Even Family: single Odd Extension Code weight Enumerator
-- statement:
--   The one-odd-row linear extension enumerator is the sum of the two cosets.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L1195-L1210
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L1195-L1210

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.Triorthogonal.BH12EvenFamily.singleOddExtensionCode_weightEnumerator {q : Nat} (a : OddRow q) :
    codeWeightEnumerator (singleOddExtensionCode a) =
      (1 + Polynomial.X ^ 8 +
        6 * Polynomial.X ^ (4 + 2 * logicalCount q)) +
      (2 * Polynomial.X ^ 7 +
        6 * Polynomial.X ^ (3 + 2 * logicalCount q)) := by sorry
