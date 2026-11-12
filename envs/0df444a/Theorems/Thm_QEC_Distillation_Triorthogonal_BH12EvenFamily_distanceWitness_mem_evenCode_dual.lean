-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_distanceWitness_mem_evenCode_dual
-- name    : QEC.Distillation.Triorthogonal.BH12EvenFamily.distanceWitness_mem_evenCode_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:05:30.063664+00:00
-- url     : https://prove2.me/theorems/be355080-f675-439f-8f13-00456b9f7366
-- title:
--   BH12 Even Family: distance Witness mem even Code dual
-- statement:
--   The weight-two representative is orthogonal to the full bottom-row span.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L631-L644
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L631-L644

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.Triorthogonal.BH12EvenFamily.distanceWitness_mem_evenCode_dual (q : Nat) :
    distanceWitness q ∈ (family q).evenCode.dual.carrier := by sorry
