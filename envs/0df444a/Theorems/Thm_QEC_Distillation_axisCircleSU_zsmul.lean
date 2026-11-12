-- Prove2me | Theorems.Thm_QEC_Distillation_axisCircleSU_zsmul
-- name    : QEC.Distillation.axisCircleSU_zsmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:10:03.624625+00:00
-- url     : https://prove2.me/theorems/86fcbb34-ca09-4e86-a818-feb1053940d5
-- title:
--   Distillation: axis Circle SU zsmul
-- statement:
--   Integer circle multiples give integer powers in the special-unitary circle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2GeneratedDensity.lean#L61-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2GeneratedDensity.lean#L61-L64

import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open GeneratedUniversality

theorem QEC.Distillation.axisCircleSU_zsmul (axis : UnitBlochAxis) (t : AddCircle (2 * Real.pi)) (z : Int) :
    axisCircleSU axis (z • t) = (axisCircleSU axis t) ^ z := by sorry
