-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_violatedGenerators_primalSweepPrefix_subset_frontier
-- name    : QEC.Coding.PeriodicCubical4.violatedGenerators_primalSweepPrefix_subset_frontier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:46:59.447818+00:00
-- url     : https://prove2.me/theorems/6677313f-3bc5-4235-a12e-5c5f478aa17d
-- title:
--   Periodic Cubical4: violated Generators primal Sweep Prefix subset frontier
-- statement:
--   Every selected check violated by a primal sweep prefix is incident on the
--   lifted moving frontier or the periodic seam.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L456-L581
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L456-L581

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.violatedGenerators_primalSweepPrefix_subset_frontier
    (z w : ZMod L) (n : Nat) (hn : n ≤ L * L) :
    (toricHamiltonian (L := L)).violatedGenerators
        (primalMembraneError (primalSweepPrefix z w n)) ⊆
      (toricHamiltonian (L := L)).incidentGeneratorUnion
        (primalSweepFrontier z w n) := by sorry
