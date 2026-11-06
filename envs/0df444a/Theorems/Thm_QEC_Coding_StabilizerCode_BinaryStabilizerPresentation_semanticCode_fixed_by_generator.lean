-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_semanticCode_fixed_by_generator
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.semanticCode_fixed_by_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:42:12.216859+00:00
-- url     : https://prove2.me/theorems/0a9fcaaf-d8a5-4dc3-bd80-1d7f7f57a8da
-- title:
--   Binary Stabilizer Presentation: semantic Code fixed by generator
-- statement:
--   The generated semantic code is fixed by every selected concrete Pauli generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Parameters.lean#L63-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Parameters.lean#L63-L71

import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Coding_Stabilizer_Parameters
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
universe u v
open QEC.Coding.StabilizerCode
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
open QEC.Coding.StabilizerCode.BinaryStabilizerPresentation

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.semanticCode_fixed_by_generator
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    {ψ : Semantics.Qubit.QubitRegister ι}
    (hψ : ψ ∈ P.semanticCode.carrier) (j : κ) :
    toQubitOperator (P.generators j) ψ = ψ := by sorry
