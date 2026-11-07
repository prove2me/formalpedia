-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_mem_syndromeSupport
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.mem_syndromeSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:23:59.102496+00:00
-- url     : https://prove2.me/theorems/d9afc3a4-1b2e-4cb6-927a-cdc3f63301f1
-- title:
--   Local Stabilizer Hamiltonian: mem syndrome Support
-- statement:
--   The Local Stabilizer Hamiltonian construction uses the mem syndrome Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Energy.lean#L80-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Energy.lean#L80-L85

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.mem_syndromeSupport
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) (j : κ) :
    j ∈ H.syndromeSupport E ↔
      stabilizerSyndrome H.generators E j = 1 := by sorry
