-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_btExcessEnergy_congr_generators
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_congr_generators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:53:58.610472+00:00
-- url     : https://prove2.me/theorems/574b88dd-9855-4ae3-a471-a8cb4a2f67fa
-- title:
--   Local Stabilizer Hamiltonian: bt Excess Energy congr generators
-- statement:
--   The combinatorial energy depends only on the literal selected generator family,
--   not on the remaining locality metadata of its Hamiltonian presentation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Energy.lean#L243-L247
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Energy.lean#L243-L247

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_congr_generators
    (H K : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (hgenerators : H.generators = K.generators) (E : Binary ι) :
    H.btExcessEnergy E = K.btExcessEnergy E := by sorry
