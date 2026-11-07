-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_btExcessEnergy_binaryMul_generated
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_binaryMul_generated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:55:27.672642+00:00
-- url     : https://prove2.me/theorems/3ee908b2-c120-44e2-ab24-eaf3e57bf9ca
-- title:
--   Local Stabilizer Hamiltonian: bt Excess Energy binary Mul generated
-- statement:
--   Selected energy is invariant under multiplication by a generated stabilizer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L291-L309
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L291-L309

import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
open scoped Classical
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
open QEC.Coding.StabilizerCode QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_binaryMul_generated
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E S : Binary ι) (hS : S ∈ H.code.1.generatedGroup) :
    H.btExcessEnergy (binaryMul E S) = H.btExcessEnergy E := by sorry
