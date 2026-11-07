-- Prove2me | Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_alphabetSize_pos
-- name    : QEC.QLDPC.FiniteQuditCheckPresentation.alphabetSize_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:53:38.358197+00:00
-- url     : https://prove2.me/theorems/f3750465-1ba4-4708-a498-e29bce0aed4f
-- title:
--   Finite Qudit Check Presentation: alphabet Size pos
-- statement:
--   The alphabet has positive local dimension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L210-L212
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L210-L212

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
set_option autoImplicit false
noncomputable section
open QEC
open QEC.QLDPC
universe u v
open QEC.QLDPC.FiniteQuditCheckPresentation
variable {ι : Type u} {κ : Type v}
variable [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem QEC.QLDPC.FiniteQuditCheckPresentation.alphabetSize_pos (P : FiniteQuditCheckPresentation ι κ) :
    0 < P.alphabetSize := by sorry
