-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalSquareProjection_frame_primalSectorMembrane
-- name    : QEC.Coding.PeriodicCubical4.primalSquareProjection_frame_primalSectorMembrane
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:30:29.686413+00:00
-- url     : https://prove2.me/theorems/d269a285-237d-4fa2-b641-541fea9060e2
-- title:
--   Periodic Cubical4: primal Square Projection frame primal Sector Membrane
-- statement:
--   The Periodic Cubical4 construction uses the primal Square Projection frame primal Sector Membrane property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L910-L924
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L910-L924

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.primalSquareProjection_frame_primalSectorMembrane
    {L : Nat} [NeZero L] [Fact (1 < L)]
    (s : MembraneSector) (p : Plane) (hp : p ∈ s.1) :
    primalSquareProjection (framePlaquetteWord p (primalSectorMembrane s)) =
      (fun _ _ => 1 : BinarySquare.Grid L) := by sorry
