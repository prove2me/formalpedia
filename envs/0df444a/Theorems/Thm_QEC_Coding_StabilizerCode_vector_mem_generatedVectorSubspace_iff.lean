-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_vector_mem_generatedVectorSubspace_iff
-- name    : QEC.Coding.StabilizerCode.vector_mem_generatedVectorSubspace_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:43:37.606139+00:00
-- url     : https://prove2.me/theorems/4da87529-27d2-4cab-8473-670ce7983a25
-- title:
--   Stabilizer Code: vector mem generated Vector Subspace iff
-- statement:
--   Up-to-sign generated-group membership is exactly vector-subspace membership.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L179-L187
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L179-L187

import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Coding_Stabilizer_Symplectic
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_Stabilizer_Detectability
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
universe u
open QEC.Coding.StabilizerCode
open PauliSymplectic
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Coding.StabilizerCode.vector_mem_generatedVectorSubspace_iff
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    (E : Binary ι) :
    E.vector ∈ Q.generatedVectorSubspace ↔ Q.InGeneratedGroupUpToSign E := by sorry
