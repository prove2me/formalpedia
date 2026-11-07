-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_dualLoopLength_dualXYMembrane
-- name    : QEC.Coding.PeriodicCubical4.dualLoopLength_dualXYMembrane
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:32:38.60624+00:00
-- url     : https://prove2.me/theorems/3c9d756f-1cfc-4fbe-964a-175b6cb23f5f
-- title:
--   Periodic Cubical4: dual Loop Length dual XYMembrane
-- statement:
--   The Periodic Cubical4 construction uses the dual Loop Length dual XYMembrane property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L1022-L1025
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L1022-L1025

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.dualLoopLength_dualXYMembrane (x y : ZMod L) :
    dualLoopLength (dualXYMembrane x y) = 0 := by sorry
