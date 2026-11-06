-- Prove2me | Theorems.Thm_QEC_Bounds_localExtension_adjoint
-- name    : QEC.Bounds.localExtension_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:08:33.764207+00:00
-- url     : https://prove2.me/theorems/4de5e785-2683-4e92-aca5-df3231f9ca57
-- title:
--   Bounds: local Extension adjoint
-- statement:
--   Identity extension commutes with taking finite-dimensional adjoints.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L119-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L119-L125

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

theorem QEC.Bounds.localExtension_adjoint {ι : Type u} [Fintype ι] [DecidableEq ι]
    {q : ι → Nat} (S : Semantics.QuditSubsystem q)
    (A : Semantics.Operator S.selectedSystem) :
    LinearMap.adjoint (S.extendLocalToRegister A) =
      S.extendLocalToRegister (LinearMap.adjoint A) := by sorry
