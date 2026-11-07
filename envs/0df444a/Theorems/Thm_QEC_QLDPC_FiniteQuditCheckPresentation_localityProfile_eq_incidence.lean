-- Prove2me | Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_localityProfile_eq_incidence
-- name    : QEC.QLDPC.FiniteQuditCheckPresentation.localityProfile_eq_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:54:59.324078+00:00
-- url     : https://prove2.me/theorems/7ea3d5e6-cfc5-41ae-8160-28ae9b0d3b29
-- title:
--   Finite Qudit Check Presentation: locality Profile eq incidence
-- statement:
--   The presentation's locality profile is exactly its incidence profile.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L303-L306
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L303-L306

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

theorem QEC.QLDPC.FiniteQuditCheckPresentation.localityProfile_eq_incidence
    (P : FiniteQuditCheckPresentation ι κ) :
    P.localityProfile = P.incidence.localityProfile := by sorry
