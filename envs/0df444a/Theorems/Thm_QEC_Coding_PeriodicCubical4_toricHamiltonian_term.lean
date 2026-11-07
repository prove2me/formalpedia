-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_toricHamiltonian_term
-- name    : QEC.Coding.PeriodicCubical4.toricHamiltonian_term
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:51:31.640263+00:00
-- url     : https://prove2.me/theorems/56421b95-ec16-4fd0-a41a-9e0637bafafe
-- title:
--   Periodic Cubical4: toric Hamiltonian term
-- statement:
--   The Periodic Cubical4 construction uses the toric Hamiltonian term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Hamiltonian.lean#L496-L499
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Hamiltonian.lean#L496-L499

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Cellulation
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Hamiltonian
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.toricHamiltonian_term (j : Sum (Link L) (Cube L)) :
    (toricHamiltonian (L := L)).term j =
      -toQubitOperator (toricGenerator j) := by sorry

attribute [defeq] QEC.Coding.PeriodicCubical4.toricHamiltonian_term
