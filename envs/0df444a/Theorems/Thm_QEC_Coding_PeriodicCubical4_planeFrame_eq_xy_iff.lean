-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_planeFrame_eq_xy_iff
-- name    : QEC.Coding.PeriodicCubical4.planeFrame_eq_xy_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:22:28.338572+00:00
-- url     : https://prove2.me/theorems/bad5e923-11b6-4c96-919e-9d673e19d070
-- title:
--   Periodic Cubical4: plane Frame eq xy iff
-- statement:
--   The Periodic Cubical4 construction uses the plane Frame eq xy iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L613-L615
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L613-L615

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.planeFrame_eq_xy_iff (p q : Plane) :
    planeFrame p q = .xy ↔ q = p := by sorry
