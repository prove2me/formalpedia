-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_distanceWitness_pair_even
-- name    : QEC.Distillation.Triorthogonal.BH12EvenFamily.distanceWitness_pair_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:05:15.378201+00:00
-- url     : https://prove2.me/theorems/3570b6f8-07a0-4630-907f-4daed561952c
-- title:
--   BH12 Even Family: distance Witness pair even
-- statement:
--   The BH12 Even Family construction uses the distance Witness pair even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L559-L567
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L559-L567

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.Triorthogonal.BH12EvenFamily.distanceWitness_pair_even (q : Nat) (r : EvenRow) :
    wordPairing (distanceWitness q) (evenWord r) = 0 := by sorry
