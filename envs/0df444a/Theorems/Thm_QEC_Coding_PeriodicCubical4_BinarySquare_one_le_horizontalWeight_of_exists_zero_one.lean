-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_BinarySquare_one_le_horizontalWeight_of_exists_zero_one
-- name    : QEC.Coding.PeriodicCubical4.BinarySquare.one_le_horizontalWeight_of_exists_zero_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:28:31.025451+00:00
-- url     : https://prove2.me/theorems/5195d9b3-72c8-4efe-bc43-6064c1447ec3
-- title:
--   Binary Square: one le horizontal Weight of exists zero one
-- statement:
--   A row containing both binary values has at least one open horizontal
--   boundary edge.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L103-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L103-L114

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
open QEC.Coding.PeriodicCubical4.BinarySquare

theorem QEC.Coding.PeriodicCubical4.BinarySquare.one_le_horizontalWeight_of_exists_zero_one {n : Nat} (g : Grid n)
    (y : Fin n) (hzero : ∃ x, g y x = 0) (hone : ∃ x, g y x = 1) :
    1 ≤ HammingWeight (horizontalDerivative g y) := by sorry
