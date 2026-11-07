-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_BinarySquare_half_le_openBoundaryLength_of_fullRows_card
-- name    : QEC.Coding.PeriodicCubical4.BinarySquare.half_le_openBoundaryLength_of_fullRows_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:29:39.208197+00:00
-- url     : https://prove2.me/theorems/0f9bc5be-6e78-43ac-b55a-1cd963de873e
-- title:
--   Binary Square: half le open Boundary Length of full Rows card
-- statement:
--   A square with exactly `n / 2` completely filled rows has an open edge
--   boundary of length at least `n / 2`.  The two cases are constructive: an empty
--   row forces a transition in every column, while without an empty row each
--   non-full row forces a transition inside that row.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L221-L285
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L221-L285

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
open QEC.Coding.PeriodicCubical4.BinarySquare

theorem QEC.Coding.PeriodicCubical4.BinarySquare.half_le_openBoundaryLength_of_fullRows_card {n : Nat} (g : Grid n)
    (hcard : (fullRows g).card = n / 2) :
    n / 2 ≤ openBoundaryLength g := by sorry
