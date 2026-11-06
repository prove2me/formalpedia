-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_not_noInformationOn_fullRegion
-- name    : QEC.Semantics.QuditSubsystem.not_noInformationOn_fullRegion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:31:51.631342+00:00
-- url     : https://prove2.me/theorems/b33c4344-cefd-4b97-bf70-2092e5f8dc23
-- title:
--   Qudit Subsystem: not no Information On full Region
-- statement:
--   Two orthogonal encoded states distinguish an actual full-region measurement.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/FiniteMeasurementDistance.lean#L55-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/FiniteMeasurementDistance.lean#L55-L76

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.QuditSubsystem
open scoped BigOperators
universe u
variable {J : Type u} [Fintype J] [DecidableEq J] (q : J → Nat)

theorem QEC.Semantics.QuditSubsystem.not_noInformationOn_fullRegion (C : QuantumCode (Qudit.QuditRegister q))
    (hq : ∀ j, 0 < q j) (x y : Qudit.QuditRegister q)
    (hx : x ∈ C.carrier) (hy : y ∈ C.carrier)
    (hxx : inner Complex x x = 1) (hyy : inner Complex y y = 1)
    (hxy : inner Complex x y = 0) : ¬ NoInformationOn C (fullRegion q) := by sorry
