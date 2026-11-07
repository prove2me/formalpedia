-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_toricHamiltonian_generators
-- name    : QEC.Coding.PeriodicCubical4.toricHamiltonian_generators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:51:44.527591+00:00
-- url     : https://prove2.me/theorems/c8d44b19-f3e8-4ce8-8c0e-be73ae938d6d
-- title:
--   Periodic Cubical4: toric Hamiltonian generators
-- statement:
--   The Periodic Cubical4 construction uses the toric Hamiltonian generators property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Hamiltonian.lean#L485-L487
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Hamiltonian.lean#L485-L487

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

theorem QEC.Coding.PeriodicCubical4.toricHamiltonian_generators :
    (toricHamiltonian (L := L)).generators = toricGenerator := by sorry

attribute [defeq] QEC.Coding.PeriodicCubical4.toricHamiltonian_generators
