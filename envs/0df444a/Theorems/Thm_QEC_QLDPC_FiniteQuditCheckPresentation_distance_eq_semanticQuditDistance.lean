-- Prove2me | Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_distance_eq_semanticQuditDistance
-- name    : QEC.QLDPC.FiniteQuditCheckPresentation.distance_eq_semanticQuditDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:53:54.149772+00:00
-- url     : https://prove2.me/theorems/94ba370d-09f6-4619-bfd3-64c58a0da1c8
-- title:
--   Finite Qudit Check Presentation: distance eq semantic Qudit Distance
-- statement:
--   The presentation's distance is the semantic local-operator distance of its code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L278-L282
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L278-L282

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

theorem QEC.QLDPC.FiniteQuditCheckPresentation.distance_eq_semanticQuditDistance
    (P : FiniteQuditCheckPresentation ι κ) :
    P.distance = semanticQuditDistance
      (uniformQuditDimensions (ι := ι) P.alphabetSize) P.code := by sorry
