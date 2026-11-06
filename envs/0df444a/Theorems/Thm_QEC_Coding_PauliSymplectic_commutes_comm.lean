-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_commutes_comm
-- name    : QEC.Coding.PauliSymplectic.commutes_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:45:03.626104+00:00
-- url     : https://prove2.me/theorems/e6dbd0ec-9013-4570-89c7-374449ab27ec
-- title:
--   Pauli Symplectic: commutes comm
-- statement:
--   Binary commutation is symmetric because the standard form is alternating.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L24-L27
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean#L24-L27

import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Coding_Stabilizer_Symplectic
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_Stabilizer_Detectability
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
universe u
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem QEC.Coding.PauliSymplectic.commutes_comm (P Q : Binary ι) : Commutes P Q ↔ Commutes Q P := by sorry
