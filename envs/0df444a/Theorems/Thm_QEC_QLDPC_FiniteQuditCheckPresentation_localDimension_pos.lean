-- Prove2me | Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_localDimension_pos
-- name    : QEC.QLDPC.FiniteQuditCheckPresentation.localDimension_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:54:22.861102+00:00
-- url     : https://prove2.me/theorems/768d50f2-bb13-43fb-baee-a47a3f736f20
-- title:
--   Finite Qudit Check Presentation: local Dimension pos
-- statement:
--   Every site in the uniform register has positive local dimension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L215-L217
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L215-L217

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

theorem QEC.QLDPC.FiniteQuditCheckPresentation.localDimension_pos (P : FiniteQuditCheckPresentation ι κ) (i : ι) :
    0 < uniformQuditDimensions (ι := ι) P.alphabetSize i := by sorry
