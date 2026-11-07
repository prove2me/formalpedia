-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalMembraneSweepPath_endpoint
-- name    : QEC.Coding.PeriodicCubical4.primalMembraneSweepPath_endpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:27:30.485283+00:00
-- url     : https://prove2.me/theorems/4baf6084-f0c6-4eff-b407-0cdade662a46
-- title:
--   Periodic Cubical4: primal Membrane Sweep Path endpoint
-- statement:
--   The Periodic Cubical4 construction uses the primal Membrane Sweep Path endpoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L875-L878
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L875-L878

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.primalMembraneSweepPath_endpoint (z w : ZMod L) :
    (primalMembraneSweepPath z w).endpoint =
      primalMembraneError (primalXYMembrane z w) := by sorry
