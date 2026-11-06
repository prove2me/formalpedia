-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_semanticCode_carrier_iff
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_semanticCode_carrier_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:42:03.658815+00:00
-- url     : https://prove2.me/theorems/18c32a1c-0fb6-4f18-8d17-980a796b95c1
-- title:
--   Binary Stabilizer Presentation: mem semantic Code carrier iff
-- statement:
--   The semantic carrier is exactly the common fixed space of the presented group.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Parameters.lean#L74-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Parameters.lean#L74-L91

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

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_semanticCode_carrier_iff
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (ψ : Semantics.Qubit.QubitRegister ι) :
    ψ ∈ P.semanticCode.carrier ↔
      ∀ G, GeneratedStabilizer P.generators G → toQubitOperator G ψ = ψ := by sorry
