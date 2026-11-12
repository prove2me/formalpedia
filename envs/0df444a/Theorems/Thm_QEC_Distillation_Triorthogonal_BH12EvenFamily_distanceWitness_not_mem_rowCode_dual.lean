-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_distanceWitness_not_mem_rowCode_dual
-- name    : QEC.Distillation.Triorthogonal.BH12EvenFamily.distanceWitness_not_mem_rowCode_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:05:35.842199+00:00
-- url     : https://prove2.me/theorems/ac848815-df07-4110-adec-f6c2ff6c0776
-- title:
--   BH12 Even Family: distance Witness not mem row Code dual
-- statement:
--   For positive `q`, the witness is not in `G⊥`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L657-L665
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L657-L665

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.Triorthogonal.BH12EvenFamily.distanceWitness_not_mem_rowCode_dual {q : Nat} (hq : 0 < q) :
    distanceWitness q ∉ (family q).rowCode.dual.carrier := by sorry
