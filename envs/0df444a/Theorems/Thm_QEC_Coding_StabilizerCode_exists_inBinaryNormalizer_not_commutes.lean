-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_exists_inBinaryNormalizer_not_commutes
-- name    : QEC.Coding.StabilizerCode.exists_inBinaryNormalizer_not_commutes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:44:53.807064+00:00
-- url     : https://prove2.me/theorems/537a498e-1c31-4eee-ad73-7fdffcd1ac6f
-- title:
--   Stabilizer Code: exists in Binary Normalizer not commutes
-- statement:
--   An outside-stabilizer normalizer vector has a normalizer partner with nonzero
--   symplectic pairing.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L207-L224
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L207-L224

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

theorem QEC.Coding.StabilizerCode.exists_inBinaryNormalizer_not_commutes
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    {E : Binary ι} (hN : Q.InBinaryNormalizer E)
    (hnotS : ¬ Q.InGeneratedGroupUpToSign E) :
    ∃ F, Q.InBinaryNormalizer F ∧ ¬ Commutes E F := by sorry
