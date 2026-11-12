-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_distanceWitness_weight
-- name    : QEC.Distillation.Triorthogonal.BH12EvenFamily.distanceWitness_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:04:37.789834+00:00
-- url     : https://prove2.me/theorems/edc61402-1705-40db-8e1f-43ae5a7e8c77
-- title:
--   BH12 Even Family: distance Witness weight
-- statement:
--   The BH12 Even Family construction uses the distance Witness weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L538-L557
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L538-L557

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.Triorthogonal.BH12EvenFamily.distanceWitness_weight (q : Nat) : HammingWeight (distanceWitness q) = 2 := by sorry
