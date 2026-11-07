-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_violatedGenerators_dualSweepPrefix_subset_frontier
-- name    : QEC.Coding.PeriodicCubical4.violatedGenerators_dualSweepPrefix_subset_frontier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:48:13.565192+00:00
-- url     : https://prove2.me/theorems/e9b094da-ea7a-4a6d-b27c-8dc055b4c5f2
-- title:
--   Periodic Cubical4: violated Generators dual Sweep Prefix subset frontier
-- statement:
--   Every selected check violated by a dual sweep prefix is incident on the
--   lifted moving frontier or the periodic seam.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L585-L710
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L585-L710

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.violatedGenerators_dualSweepPrefix_subset_frontier
    (x y : ZMod L) (n : Nat) (hn : n ≤ L * L) :
    (toricHamiltonian (L := L)).violatedGenerators
        (dualMembraneError (dualSweepPrefix x y n)) ⊆
      (toricHamiltonian (L := L)).incidentGeneratorUnion
        (dualSweepFrontier x y n) := by sorry
