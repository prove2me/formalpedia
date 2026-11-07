-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_toricHamiltonian_generators_commute
-- name    : QEC.Coding.PeriodicCubical4.toricHamiltonian_generators_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:51:29.400141+00:00
-- url     : https://prove2.me/theorems/2be580c8-c002-41d7-837c-b0748d88c418
-- title:
--   Periodic Cubical4: toric Hamiltonian generators commute
-- statement:
--   The Periodic Cubical4 construction uses the toric Hamiltonian generators commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Hamiltonian.lean#L489-L493
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Hamiltonian.lean#L489-L493

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

theorem QEC.Coding.PeriodicCubical4.toricHamiltonian_generators_commute
    (j k : Sum (Link L) (Cube L)) :
    Commutes ((toricHamiltonian (L := L)).generators j)
      ((toricHamiltonian (L := L)).generators k) := by sorry
