-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalXYMembrane_eq_indicator_sweepPlaquettes
-- name    : QEC.Coding.PeriodicCubical4.primalXYMembrane_eq_indicator_sweepPlaquettes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:29:59.241186+00:00
-- url     : https://prove2.me/theorems/35ff5031-8b45-4318-b857-9ac3bd2bd27d
-- title:
--   Periodic Cubical4: primal XYMembrane eq indicator sweep Plaquettes
-- statement:
--   The Periodic Cubical4 construction uses the primal XYMembrane eq indicator sweep Plaquettes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L131-L141
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L131-L141

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.primalXYMembrane_eq_indicator_sweepPlaquettes (z w : ZMod L) :
    primalXYMembrane z w = fun q =>
      if q ∈ (primalSweepPlaquettes z w).toFinset then 1 else 0 := by sorry
