-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_distanceWitness_pair_odd
-- name    : QEC.Distillation.Triorthogonal.BH12EvenFamily.distanceWitness_pair_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:05:37.267203+00:00
-- url     : https://prove2.me/theorems/753c2d68-f963-4d84-b944-5328520b443c
-- title:
--   BH12 Even Family: distance Witness pair odd
-- statement:
--   Every top row pairs nontrivially with the weight-two representative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L647-L654
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L647-L654

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.Triorthogonal.BH12EvenFamily.distanceWitness_pair_odd {q : Nat} (a : OddRow q) :
    wordPairing (distanceWitness q) (oddWord a) = 1 := by sorry
