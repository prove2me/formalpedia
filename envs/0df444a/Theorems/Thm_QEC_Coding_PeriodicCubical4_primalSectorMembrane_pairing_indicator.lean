-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalSectorMembrane_pairing_indicator
-- name    : QEC.Coding.PeriodicCubical4.primalSectorMembrane_pairing_indicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:30:33.238705+00:00
-- url     : https://prove2.me/theorems/5513e0ba-b5f0-4f1b-a306-38e68d901372
-- title:
--   Periodic Cubical4: primal Sector Membrane pairing indicator
-- statement:
--   The Periodic Cubical4 construction uses the primal Sector Membrane pairing indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L786-L800
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L786-L800

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.primalSectorMembrane_pairing_indicator
    {L : Nat} [NeZero L] (s : MembraneSector) (p : Plane)
    (a b : ZMod L) :
    wordPairing (dualCoordinateMembrane p a b) (primalSectorMembrane s) =
      if p ∈ s.1 then 1 else 0 := by sorry
