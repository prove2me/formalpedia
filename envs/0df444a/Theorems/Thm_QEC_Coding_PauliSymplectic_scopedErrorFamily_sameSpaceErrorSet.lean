-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_scopedErrorFamily_sameSpaceErrorSet
-- name    : QEC.Coding.PauliSymplectic.scopedErrorFamily_sameSpaceErrorSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:22:22.951941+00:00
-- url     : https://prove2.me/theorems/95202dea-e938-462f-a564-1d6ee66b74d5
-- title:
--   Pauli Symplectic: scoped Error Family same Space Error Set
-- statement:
--   The Pauli Symplectic construction uses the scoped Error Family same Space Error Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L750-L761
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L750-L761

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
open scoped BigOperators
universe u w
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι]
variable [DecidableEq ι]

theorem QEC.Coding.PauliSymplectic.scopedErrorFamily_sameSpaceErrorSet (B : Nat) :
    (scopedErrorFamily (ι := ι) B).sameSpaceErrorSet =
      scopedErrorOperators (ι := ι) B := by sorry
