-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_dimension_evenCode_dual
-- name    : QEC.Distillation.Triorthogonal.BH12EvenFamily.dimension_evenCode_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:37:07.428437+00:00
-- url     : https://prove2.me/theorems/303b0a25-2942-4591-a85b-c8fa16b7928a
-- title:
--   BH12 Even Family: dimension even Code dual
-- statement:
--   `dim G₀⊥ = 3k+5`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L500-L506
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L500-L506

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.Triorthogonal.BH12EvenFamily.dimension_evenCode_dual (q : Nat) :
    Dimension (family q).evenCode.dual = 3 * logicalCount q + 5 := by sorry
