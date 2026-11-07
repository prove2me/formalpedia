-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_BinarySquare_eq_zero_of_horizontalDerivative_eq_zero
-- name    : QEC.Coding.PeriodicCubical4.BinarySquare.eq_zero_of_horizontalDerivative_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:38:51.128527+00:00
-- url     : https://prove2.me/theorems/2f38dad7-744e-4559-94a8-c8e4bde298df
-- title:
--   Binary Square: eq zero of horizontal Derivative eq zero
-- statement:
--   If every adjacent difference on a finite line vanishes, the line is
--   constant.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L80-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L80-L99

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
open QEC.Coding.PeriodicCubical4.BinarySquare

theorem QEC.Coding.PeriodicCubical4.BinarySquare.eq_zero_of_horizontalDerivative_eq_zero {n : Nat} (g : Grid n)
    (y : Fin n) (hzero : horizontalDerivative g y = 0) (i j : Fin n) :
    g y i = g y j := by sorry
