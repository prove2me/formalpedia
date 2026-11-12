-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_oddCoset_weightEnumerator
-- name    : QEC.Distillation.Triorthogonal.BH12EvenFamily.oddCoset_weightEnumerator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:40:19.700869+00:00
-- url     : https://prove2.me/theorems/70fd7b60-c674-4771-a276-ec9901440ab1
-- title:
--   BH12 Even Family: odd Coset weight Enumerator
-- statement:
--   The source formula `W_(G₀+gᵃ)(x) = 2x⁷ + 6x^(3+2k)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L1183-L1192
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L1183-L1192

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.Triorthogonal.BH12EvenFamily.oddCoset_weightEnumerator {q : Nat} (a : OddRow q) :
    oddCosetWeightEnumerator a =
      2 * Polynomial.X ^ 7 + 6 * Polynomial.X ^ (3 + 2 * logicalCount q) := by sorry
