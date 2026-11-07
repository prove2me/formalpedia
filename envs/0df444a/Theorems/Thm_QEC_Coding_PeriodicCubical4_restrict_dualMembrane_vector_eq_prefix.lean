-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_restrict_dualMembrane_vector_eq_prefix
-- name    : QEC.Coding.PeriodicCubical4.restrict_dualMembrane_vector_eq_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:31:10.461206+00:00
-- url     : https://prove2.me/theorems/3895ea37-591e-40e0-baa6-aaa97e1d17c7
-- title:
--   Periodic Cubical4: restrict dual Membrane vector eq prefix
-- statement:
--   The Periodic Cubical4 construction uses the restrict dual Membrane vector eq prefix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L435-L452
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L435-L452

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.restrict_dualMembrane_vector_eq_prefix
    (x y : ZMod L) (n : Nat) :
    (Locality.restrictBinaryTo (dualSweepRegion x y n)
      (dualMembraneError (dualXYMembrane x y))).vector =
    (dualMembraneError (dualSweepPrefix x y n)).vector := by sorry
