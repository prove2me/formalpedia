-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_BinarySquare_fullRows_card_dist_le_one_of_oneCellStep
-- name    : QEC.Coding.PeriodicCubical4.BinarySquare.fullRows_card_dist_le_one_of_oneCellStep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:29:25.345761+00:00
-- url     : https://prove2.me/theorems/553ffe2d-4ac4-4054-8980-95ea1d46821c
-- title:
--   Binary Square: full Rows card dist le one of one Cell Step
-- statement:
--   Changing at most one cell changes the number of full rows by at most one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L133-L196
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L133-L196

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
open QEC.Coding.PeriodicCubical4.BinarySquare

theorem QEC.Coding.PeriodicCubical4.BinarySquare.fullRows_card_dist_le_one_of_oneCellStep {n : Nat} (g h : Grid n)
    (hstep : OneCellStep g h) :
    Nat.dist (fullRows g).card (fullRows h).card ≤ 1 := by sorry
