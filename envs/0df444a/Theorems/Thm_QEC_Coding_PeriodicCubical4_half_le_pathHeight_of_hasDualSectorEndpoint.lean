-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_half_le_pathHeight_of_hasDualSectorEndpoint
-- name    : QEC.Coding.PeriodicCubical4.half_le_pathHeight_of_hasDualSectorEndpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:31:24.764688+00:00
-- url     : https://prove2.me/theorems/a23a3030-e0f3-4f0a-ab22-59227668ba23
-- title:
--   Periodic Cubical4: half le path Height of has Dual Sector Endpoint
-- statement:
--   Every path to every nonzero dual coordinate-membrane sector has linear height.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1042-L1050
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1042-L1050

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.half_le_pathHeight_of_hasDualSectorEndpoint
    {L : Nat} [NeZero L] [Fact (1 < L)]
    (gamma : PauliErrorPath (ι := Plaquette L)) (s : MembraneSector)
    (hendpoint : HasDualSectorEndpoint gamma s) :
    L / 2 ≤ (toricHamiltonian (L := L)).pathHeight gamma := by sorry
