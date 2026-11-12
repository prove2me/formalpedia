-- Prove2me | Theorems.Thm_QEC_Distillation_blochPauliMatrix_mul
-- name    : QEC.Distillation.blochPauliMatrix_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:03:31.936623+00:00
-- url     : https://prove2.me/theorems/e9899fba-b383-4a3e-982d-f26ed889901b
-- title:
--   Distillation: bloch Pauli Matrix mul
-- statement:
--   The Pauli product formula for arbitrary real Bloch vectors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2NonparallelAxes.lean#L79-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2NonparallelAxes.lean#L79-L90

import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.CrossProduct
import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open Matrix

theorem QEC.Distillation.blochPauliMatrix_mul (v w : Fin 3 → Real) :
    blochPauliMatrix v * blochPauliMatrix w =
      ((v ⬝ᵥ w : Real) : Complex) • 1 +
        Complex.I • blochPauliMatrix (v ⨯₃ w) := by sorry
