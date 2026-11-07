-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_mem_violatedGenerators_frameBinary_iff
-- name    : QEC.Coding.PeriodicCubical4.mem_violatedGenerators_frameBinary_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:29:34.337502+00:00
-- url     : https://prove2.me/theorems/f0e8b5a0-64ef-457c-bce2-1d09ba5b131b
-- title:
--   Periodic Cubical4: mem violated Generators frame Binary iff
-- statement:
--   Membership in the violated-generator set is transported by the generator frame.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L493-L507
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L493-L507

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.mem_violatedGenerators_frameBinary_iff {L : Nat}
    [NeZero L] [Fact (1 < L)]
    (p : Plane) (E : Binary (Plaquette L))
    (j : Sum (Link L) (Cube L)) :
    j ∈ (toricHamiltonian (L := L)).violatedGenerators (frameBinary p E) ↔
      frameGeneratorIndex p j ∈
        (toricHamiltonian (L := L)).violatedGenerators E := by sorry
