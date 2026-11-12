-- Prove2me | Theorems.Thm_QEC_Distillation_axisCircle_zsmul
-- name    : QEC.Distillation.axisCircle_zsmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:09:50.405142+00:00
-- url     : https://prove2.me/theorems/bf5dba16-8ee6-4619-8bf0-ae39b0dc44a7
-- title:
--   Distillation: axis Circle zsmul
-- statement:
--   Integer circle multiples give integer powers of the corresponding gate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2GeneratedDensity.lean#L56-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2GeneratedDensity.lean#L56-L58

import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open GeneratedUniversality

theorem QEC.Distillation.axisCircle_zsmul (axis : UnitBlochAxis) (t : AddCircle (2 * Real.pi)) (z : Int) :
    axisCircle axis (z • t) = (axisCircle axis t) ^ z := by sorry
