-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_not_inBinaryNormalizer_iff_exists_not_commutes
-- name    : QEC.Coding.StabilizerCode.not_inBinaryNormalizer_iff_exists_not_commutes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:28:30.866192+00:00
-- url     : https://prove2.me/theorems/9abe124f-d420-452c-b1e5-7870a4319973
-- title:
--   Stabilizer Code: not in Binary Normalizer iff exists not commutes
-- statement:
--   Failure of code-level normalizer membership has a generated anticommuting witness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L227-L233
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L227-L233

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

theorem QEC.Coding.StabilizerCode.not_inBinaryNormalizer_iff_exists_not_commutes
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    (E : Binary ι) :
    ¬ Q.InBinaryNormalizer E ↔
      ∃ S, S ∈ Q.generatedGroup ∧ ¬ Commutes E S := by sorry
