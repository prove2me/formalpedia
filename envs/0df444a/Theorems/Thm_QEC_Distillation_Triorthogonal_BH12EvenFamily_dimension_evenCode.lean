-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_dimension_evenCode
-- name    : QEC.Distillation.Triorthogonal.BH12EvenFamily.dimension_evenCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:04:53.2608+00:00
-- url     : https://prove2.me/theorems/cdc3b101-4a53-47f2-88e8-970130b7dff4
-- title:
--   BH12 Even Family: dimension even Code
-- statement:
--   `dim G₀ = 3`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L471-L474
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L471-L474

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.Triorthogonal.BH12EvenFamily.dimension_evenCode (q : Nat) : Dimension (family q).evenCode = 3 := by sorry
