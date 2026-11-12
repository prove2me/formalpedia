-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_zero_relativeSector_empty
-- name    : QEC.Distillation.Triorthogonal.BH12EvenFamily.zero_relativeSector_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:05:49.22529+00:00
-- url     : https://prove2.me/theorems/8d51e238-890c-4dbd-8e4f-181f3cc44933
-- title:
--   BH12 Even Family: zero relative Sector empty
-- statement:
--   Consequently the endpoint `q=0` relative sector is empty.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L707-L710
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L707-L710

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.Triorthogonal.BH12EvenFamily.zero_relativeSector_empty (x : Word (ZMod 2) (Column 0)) :
    x ∈ (family 0).evenCode.dual.carrier ↔
      x ∈ (family 0).rowCode.dual.carrier := by sorry
