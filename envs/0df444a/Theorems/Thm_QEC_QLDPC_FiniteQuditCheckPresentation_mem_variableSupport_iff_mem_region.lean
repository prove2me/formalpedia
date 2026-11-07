-- Prove2me | Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_mem_variableSupport_iff_mem_region
-- name    : QEC.QLDPC.FiniteQuditCheckPresentation.mem_variableSupport_iff_mem_region
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:53:49.456209+00:00
-- url     : https://prove2.me/theorems/2c3ced7c-24da-43ea-b468-7650126a3b58
-- title:
--   Finite Qudit Check Presentation: mem variable Support iff mem region
-- statement:
--   Variable support lists exactly the checks whose local region contains the coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L256-L261
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L256-L261

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

theorem QEC.QLDPC.FiniteQuditCheckPresentation.mem_variableSupport_iff_mem_region
    (P : FiniteQuditCheckPresentation ι κ)
    (checkIndex : κ) (coordinate : ι) :
    checkIndex ∈ P.incidence.variableSupport coordinate ↔
      coordinate ∈ (P.checks checkIndex).region.selected := by sorry
