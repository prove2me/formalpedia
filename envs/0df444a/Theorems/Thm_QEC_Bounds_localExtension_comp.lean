-- Prove2me | Theorems.Thm_QEC_Bounds_localExtension_comp
-- name    : QEC.Bounds.localExtension_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:09:22.81734+00:00
-- url     : https://prove2.me/theorems/066bdaf5-cfde-4588-9ac7-5e6c40626dc3
-- title:
--   Bounds: local Extension comp
-- statement:
--   Identity extension respects composition of local operators.  This is the
--   algebraic local-extension fact used to instantiate projector laws.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L107-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L107-L116

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators
universe u v

theorem QEC.Bounds.localExtension_comp {ι : Type u} [Fintype ι] [DecidableEq ι]
    {q : ι → Nat} (S : Semantics.QuditSubsystem q)
    (A B : Semantics.Operator S.selectedSystem) :
    (S.extendLocalToRegister A).comp (S.extendLocalToRegister B) =
      S.extendLocalToRegister (A.comp B) := by sorry
