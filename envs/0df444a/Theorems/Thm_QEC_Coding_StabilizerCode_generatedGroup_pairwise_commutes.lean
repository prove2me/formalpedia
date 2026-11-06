-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_generatedGroup_pairwise_commutes
-- name    : QEC.Coding.StabilizerCode.generatedGroup_pairwise_commutes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:48:15.365696+00:00
-- url     : https://prove2.me/theorems/1e314961-c1a8-474a-9ec9-2b652aadacdf
-- title:
--   Stabilizer Code: generated Group pairwise commutes
-- statement:
--   The generated stabilizer remains pairwise symplectically commuting.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L138-L155
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L138-L155

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

theorem QEC.Coding.StabilizerCode.generatedGroup_pairwise_commutes
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    {P R : Binary ι} (hP : P ∈ Q.generatedGroup) (hR : R ∈ Q.generatedGroup) :
    Commutes P R := by sorry
