-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalSectorMembrane_pairing
-- name    : QEC.Coding.PeriodicCubical4.primalSectorMembrane_pairing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:23:25.560196+00:00
-- url     : https://prove2.me/theorems/7bf6ee3d-9461-4df5-a8e4-ac7ddb55a3bf
-- title:
--   Periodic Cubical4: primal Sector Membrane pairing
-- statement:
--   The Periodic Cubical4 construction uses the primal Sector Membrane pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L687-L696
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L687-L696

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.primalSectorMembrane_pairing
    {L : Nat} [NeZero L] (s : MembraneSector) (p : Plane) (hp : p ∈ s.1)
    (a b : ZMod L) :
    wordPairing (dualCoordinateMembrane p a b) (primalSectorMembrane s) = 1 := by sorry
