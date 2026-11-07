-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_BinarySquare_one_le_verticalWeight_of_exists_zero_one
-- name    : QEC.Coding.PeriodicCubical4.BinarySquare.one_le_verticalWeight_of_exists_zero_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:38:51.423792+00:00
-- url     : https://prove2.me/theorems/74a7d57a-cd29-46be-bbff-19db783c7039
-- title:
--   Binary Square: one le vertical Weight of exists zero one
-- statement:
--   A column containing both binary values has at least one open vertical
--   boundary edge.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L118-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L118-L125

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
open QEC.Coding.PeriodicCubical4.BinarySquare

theorem QEC.Coding.PeriodicCubical4.BinarySquare.one_le_verticalWeight_of_exists_zero_one {n : Nat} (g : Grid n)
    (x : Fin n) (hzero : ∃ y, g y x = 0) (hone : ∃ y, g y x = 1) :
    1 ≤ HammingWeight (verticalDerivative g x) := by sorry
