-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_zero_evenCode_dual_eq_rowCode_dual
-- name    : QEC.Distillation.Triorthogonal.BH12EvenFamily.zero_evenCode_dual_eq_rowCode_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:05:50.373942+00:00
-- url     : https://prove2.me/theorems/ed0e8eab-aa7b-4ab0-900b-6bb1a0b7d1eb
-- title:
--   BH12 Even Family: zero even Code dual eq row Code dual
-- statement:
--   At `q=0`, there is no odd sector and the two relevant dual codes coincide.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L694-L704
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L694-L704

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.Triorthogonal.BH12EvenFamily.zero_evenCode_dual_eq_rowCode_dual :
    (family 0).evenCode.dual.carrier = (family 0).rowCode.dual.carrier := by sorry
