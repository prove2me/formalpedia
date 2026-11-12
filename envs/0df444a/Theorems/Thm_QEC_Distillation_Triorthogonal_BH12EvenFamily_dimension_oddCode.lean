-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_dimension_oddCode
-- name    : QEC.Distillation.Triorthogonal.BH12EvenFamily.dimension_oddCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:36:33.686648+00:00
-- url     : https://prove2.me/theorems/a4c8dd67-f716-4443-ba5d-a511a138ddc7
-- title:
--   BH12 Even Family: dimension odd Code
-- statement:
--   `dim G₁ = k`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L477-L480
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L477-L480

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.Triorthogonal.BH12EvenFamily.dimension_oddCode (q : Nat) :
    Dimension (family q).oddCode = logicalCount q := by sorry
