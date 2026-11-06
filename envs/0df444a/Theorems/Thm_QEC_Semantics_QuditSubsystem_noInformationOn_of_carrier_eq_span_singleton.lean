-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_noInformationOn_of_carrier_eq_span_singleton
-- name    : QEC.Semantics.QuditSubsystem.noInformationOn_of_carrier_eq_span_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:18:03.65721+00:00
-- url     : https://prove2.me/theorems/7a63d6ce-4774-4db2-82fb-97734a976e2d
-- title:
--   Qudit Subsystem: no Information On of carrier eq span singleton
-- statement:
--   A nonzero one-dimensional code reveals no information to any local valid effect.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L618-L624
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L618-L624

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

theorem QEC.Semantics.QuditSubsystem.noInformationOn_of_carrier_eq_span_singleton
    (C : QuantumCode (Qudit.QuditRegister q)) (S : QuditSubsystem q)
    (v : Qudit.QuditRegister q) (hv : v ≠ 0) (hC : C.carrier = Complex ∙ v) :
    NoInformationOn C S := by sorry
