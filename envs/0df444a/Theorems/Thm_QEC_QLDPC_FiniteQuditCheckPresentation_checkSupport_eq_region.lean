-- Prove2me | Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_checkSupport_eq_region
-- name    : QEC.QLDPC.FiniteQuditCheckPresentation.checkSupport_eq_region
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:53:46.474631+00:00
-- url     : https://prove2.me/theorems/dc209acb-7319-42d1-8023-700e7fd17468
-- title:
--   Finite Qudit Check Presentation: check Support eq region
-- statement:
--   The incidence support of a check is its explicitly selected local region.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L247-L252
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L247-L252

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

theorem QEC.QLDPC.FiniteQuditCheckPresentation.checkSupport_eq_region (P : FiniteQuditCheckPresentation ι κ)
    (checkIndex : κ) :
    P.incidence.checkSupport checkIndex =
      (P.checks checkIndex).region.selected := by sorry
