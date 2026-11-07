-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_dualMembraneSweepPath_endpoint
-- name    : QEC.Coding.PeriodicCubical4.dualMembraneSweepPath_endpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:27:23.295572+00:00
-- url     : https://prove2.me/theorems/7073a418-7c64-4d96-ac5d-79458d2e23f8
-- title:
--   Periodic Cubical4: dual Membrane Sweep Path endpoint
-- statement:
--   The Periodic Cubical4 construction uses the dual Membrane Sweep Path endpoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L880-L883
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L880-L883

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.dualMembraneSweepPath_endpoint (x y : ZMod L) :
    (dualMembraneSweepPath x y).endpoint =
      dualMembraneError (dualXYMembrane x y) := by sorry
