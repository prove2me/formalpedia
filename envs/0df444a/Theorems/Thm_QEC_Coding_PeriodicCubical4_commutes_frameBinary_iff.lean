-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_commutes_frameBinary_iff
-- name    : QEC.Coding.PeriodicCubical4.commutes_frameBinary_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:24:22.802223+00:00
-- url     : https://prove2.me/theorems/bdf34684-47f0-44bf-b4e4-e9bbcdbb99f8
-- title:
--   Periodic Cubical4: commutes frame Binary iff
-- statement:
--   The Periodic Cubical4 construction uses the commutes frame Binary iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L484-L490
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L484-L490

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.commutes_frameBinary_iff {L : Nat} [NeZero L]
    (p : Plane) (E F : Binary (Plaquette L)) :
    Commutes (frameBinary p E) (frameBinary p F) ↔ Commutes E F := by sorry
