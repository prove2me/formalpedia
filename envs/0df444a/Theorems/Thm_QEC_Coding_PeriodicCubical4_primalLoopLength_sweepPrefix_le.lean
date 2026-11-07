-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalLoopLength_sweepPrefix_le
-- name    : QEC.Coding.PeriodicCubical4.primalLoopLength_sweepPrefix_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:48:57.066764+00:00
-- url     : https://prove2.me/theorems/0e0dcf50-90e2-450f-a4e9-aebca10d78c1
-- title:
--   Periodic Cubical4: primal Loop Length sweep Prefix le
-- statement:
--   The primal defect loop exposed by any row-major prefix has linear length.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L713-L730
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L713-L730

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.primalLoopLength_sweepPrefix_le
    (z w : ZMod L) (n : Nat) (hn : n ≤ L * L) :
    primalLoopLength (primalSweepPrefix z w n) ≤ 32 * L := by sorry
