-- Prove2me | Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_detectable_of_card_lt_distance
-- name    : QEC.QLDPC.FiniteQuditCheckPresentation.detectable_of_card_lt_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:54:37.235346+00:00
-- url     : https://prove2.me/theorems/b731d296-5d99-46fc-8ad0-c71da9ca3c2c
-- title:
--   Finite Qudit Check Presentation: detectable of card lt distance
-- statement:
--   Every local operator below the derived distance is detectable by the code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L291-L300
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L291-L300

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

theorem QEC.QLDPC.FiniteQuditCheckPresentation.detectable_of_card_lt_distance
    (P : FiniteQuditCheckPresentation ι κ)
    (region : Semantics.QuditSubsystem
      (uniformQuditDimensions (ι := ι) P.alphabetSize))
    (hcard : Fintype.card region.SelectedCoordinates < P.distance)
    (localOperator : Semantics.Operator region.selectedSystem) :
    Semantics.DetectableOn P.code
      (region.extendLocalToRegister localOperator) := by sorry
