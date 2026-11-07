-- Prove2me | Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_incidence_iff_mem_region
-- name    : QEC.QLDPC.FiniteQuditCheckPresentation.incidence_iff_mem_region
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:52:14.690205+00:00
-- url     : https://prove2.me/theorems/3abf25a4-1098-49a5-a53f-e0618ceba552
-- title:
--   Finite Qudit Check Presentation: incidence iff mem region
-- statement:
--   A coordinate is incident to a check exactly when it lies in that check's region.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L240-L244
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L240-L244

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

theorem QEC.QLDPC.FiniteQuditCheckPresentation.incidence_iff_mem_region (P : FiniteQuditCheckPresentation ι κ)
    (checkIndex : κ) (coordinate : ι) :
    P.incidence.incident checkIndex coordinate ↔
      coordinate ∈ (P.checks checkIndex).region.selected := by sorry
