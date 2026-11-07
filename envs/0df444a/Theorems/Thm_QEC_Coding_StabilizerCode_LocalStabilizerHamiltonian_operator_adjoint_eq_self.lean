-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_operator_adjoint_eq_self
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.operator_adjoint_eq_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:33:49.348066+00:00
-- url     : https://prove2.me/theorems/ab7bec81-6b9b-4368-b699-1120833cba08
-- title:
--   Local Stabilizer Hamiltonian: operator adjoint eq self
-- statement:
--   The finite unit-coefficient Hamiltonian is self-adjoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/LocalHamiltonian.lean#L158-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/LocalHamiltonian.lean#L158-L161

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_Core_Definitions
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open PauliSymplectic
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.operator_adjoint_eq_self
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) :
    LinearMap.adjoint H.operator = H.operator := by sorry
