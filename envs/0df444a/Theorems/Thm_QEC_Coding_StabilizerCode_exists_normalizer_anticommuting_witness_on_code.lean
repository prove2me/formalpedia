-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_exists_normalizer_anticommuting_witness_on_code
-- name    : QEC.Coding.StabilizerCode.exists_normalizer_anticommuting_witness_on_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:29:25.763495+00:00
-- url     : https://prove2.me/theorems/93c2c657-39a9-47fc-95f0-5c1c708ec008
-- title:
--   Stabilizer Code: exists normalizer anticommuting witness on code
-- statement:
--   A logical partner together with a nonzero code witness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L466-L476
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L466-L476

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

theorem QEC.Coding.StabilizerCode.exists_normalizer_anticommuting_witness_on_code
    (Q : SourceValidBinary ι) (E : Binary ι)
    (hN : Q.1.InBinaryNormalizer E)
    (hnotS : ¬ Q.1.InGeneratedGroupUpToSign E) :
    ∃ F ψ,
      Q.1.InBinaryNormalizer F ∧
      ψ ∈ Q.1.code.carrier ∧ ψ ≠ 0 ∧ ¬ Commutes E F := by sorry
