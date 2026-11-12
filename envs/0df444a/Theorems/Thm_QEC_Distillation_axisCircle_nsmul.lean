-- Prove2me | Theorems.Thm_QEC_Distillation_axisCircle_nsmul
-- name    : QEC.Distillation.axisCircle_nsmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:58:29.265344+00:00
-- url     : https://prove2.me/theorems/3165448a-8cd0-4672-b8fb-c3103e30328d
-- title:
--   Distillation: axis Circle nsmul
-- statement:
--   Natural circle multiples give natural powers of the corresponding gate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2AxisCircle.lean#L259-L264
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2AxisCircle.lean#L259-L264

import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open GeneratedUniversality

theorem QEC.Distillation.axisCircle_nsmul (axis : UnitBlochAxis) (t : AddCircle (2 * Real.pi)) (n : Nat) :
    axisCircle axis (n • t) = (axisCircle axis t) ^ n := by sorry
