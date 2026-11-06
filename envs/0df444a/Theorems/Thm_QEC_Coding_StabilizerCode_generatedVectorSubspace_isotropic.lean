-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_generatedVectorSubspace_isotropic
-- name    : QEC.Coding.StabilizerCode.generatedVectorSubspace_isotropic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:44:00.126335+00:00
-- url     : https://prove2.me/theorems/2f8980e6-704c-4b1b-850c-2156ad6d660d
-- title:
--   Stabilizer Code: generated Vector Subspace isotropic
-- statement:
--   The generated-vector subspace is isotropic.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L158-L164
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L158-L164

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

theorem QEC.Coding.StabilizerCode.generatedVectorSubspace_isotropic
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι)) :
    Q.generatedVectorSubspace ≤
      FiniteSymplectic.form.orthogonal Q.generatedVectorSubspace := by sorry
