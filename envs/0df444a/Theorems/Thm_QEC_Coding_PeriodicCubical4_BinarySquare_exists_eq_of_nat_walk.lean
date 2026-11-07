-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_BinarySquare_exists_eq_of_nat_walk
-- name    : QEC.Coding.PeriodicCubical4.BinarySquare.exists_eq_of_nat_walk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:30:46.940191+00:00
-- url     : https://prove2.me/theorems/06f6eb65-6017-499d-926b-edff00f5c94f
-- title:
--   Binary Square: exists eq of nat walk
-- statement:
--   A nearest-neighbour walk of natural numbers hits every intermediate
--   integer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L200-L215
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L200-L215

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
open QEC.Coding.PeriodicCubical4.BinarySquare

theorem QEC.Coding.PeriodicCubical4.BinarySquare.exists_eq_of_nat_walk
    (a : Nat → Nat) (N target : Nat)
    (hstart : a 0 ≤ target) (hend : target ≤ a N)
    (hstep : ∀ k < N, Nat.dist (a (k + 1)) (a k) ≤ 1) :
    ∃ k ≤ N, a k = target := by sorry
