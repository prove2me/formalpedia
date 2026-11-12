-- Prove2me | Theorems.Thm_QEC_Distillation_blochPauliMatrix_commutator
-- name    : QEC.Distillation.blochPauliMatrix_commutator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:03:34.055072+00:00
-- url     : https://prove2.me/theorems/d48b6131-ee84-4703-b72a-896f79889901
-- title:
--   Distillation: bloch Pauli Matrix commutator
-- statement:
--   The Pauli commutator is twice `i` times the Bloch cross product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2NonparallelAxes.lean#L93-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2NonparallelAxes.lean#L93-L102

import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.CrossProduct
import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open Matrix

theorem QEC.Distillation.blochPauliMatrix_commutator (v w : Fin 3 → Real) :
    blochPauliMatrix v * blochPauliMatrix w - blochPauliMatrix w * blochPauliMatrix v =
      ((2 : Complex) * Complex.I) • blochPauliMatrix (v ⨯₃ w) := by sorry
