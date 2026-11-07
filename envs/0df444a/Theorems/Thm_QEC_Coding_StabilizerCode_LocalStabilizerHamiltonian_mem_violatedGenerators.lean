-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_mem_violatedGenerators
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.mem_violatedGenerators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:23:53.538823+00:00
-- url     : https://prove2.me/theorems/6bf80398-7b78-42fe-8f3c-c6bd7377ef64
-- title:
--   Local Stabilizer Hamiltonian: mem violated Generators
-- statement:
--   The Local Stabilizer Hamiltonian construction uses the mem violated Generators property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Energy.lean#L73-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Energy.lean#L73-L77

import Definitions.Def_QEC_Coding_Stabilizer_ErrorPath
import Definitions.Def_QEC_Coding_Stabilizer_Energy
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
open PauliSymplectic
open scoped Classical
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.mem_violatedGenerators
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) (j : κ) :
    j ∈ H.violatedGenerators E ↔ ¬ Commutes E (H.generators j) := by sorry
