-- Prove2me | Theorems.Thm_QEC_Distillation_coordinateSupport_disjoint
-- name    : QEC.Distillation.coordinateSupport_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:44:04.031211+00:00
-- url     : https://prove2.me/theorems/dff91987-c5e3-48ee-9e21-6fa0ef389478
-- title:
--   Distillation: coordinate Support disjoint
-- statement:
--   Distinct within-copy sites determine disjoint tagged three-copy supports.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/Register.lean#L100-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/Register.lean#L100-L107

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation
universe u
variable {F ι : Type u} [Field F] [Fintype F]

theorem QEC.Distillation.coordinateSupport_disjoint [Fintype ι] [DecidableEq ι]
    {first second : ι} (hne : first ≠ second) :
    Disjoint (coordinateSupport first) (coordinateSupport second) := by sorry
