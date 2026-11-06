-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_vector_mem_orthogonal_iff_inBinaryNormalizer
-- name    : QEC.Coding.StabilizerCode.vector_mem_orthogonal_iff_inBinaryNormalizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:44:07.699982+00:00
-- url     : https://prove2.me/theorems/3b4e1e9a-63fc-4476-bc02-64fd32f2099b
-- title:
--   Stabilizer Code: vector mem orthogonal iff in Binary Normalizer
-- statement:
--   Normalizer membership is membership in the generated subspace's orthogonal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L190-L201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L190-L201

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

theorem QEC.Coding.StabilizerCode.vector_mem_orthogonal_iff_inBinaryNormalizer
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    (E : Binary ι) :
    E.vector ∈ FiniteSymplectic.form.orthogonal Q.generatedVectorSubspace ↔
      Q.InBinaryNormalizer E := by sorry
