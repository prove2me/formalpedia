-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_lindbladJumpTerm_smul
-- name    : QEC.Semantics.Davies.lindbladJumpTerm_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:28:19.550615+00:00
-- url     : https://prove2.me/theorems/12032763-0f44-4a4c-ab8c-4c03478ed475
-- title:
--   Davies: lindblad Jump Term smul
-- statement:
--   Scaling a genuine jump scales its quadratic dissipator by the squared modulus.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L69-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L69-L73

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Stationarity
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical ThermalEncoding
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem QEC.Semantics.Davies.lindbladJumpTerm_smul (J : Operator V) (c : ℂ) (F : Operator V) :
    lindbladJumpTerm (c • J) F = (c * star c) • lindbladJumpTerm J F := by sorry
