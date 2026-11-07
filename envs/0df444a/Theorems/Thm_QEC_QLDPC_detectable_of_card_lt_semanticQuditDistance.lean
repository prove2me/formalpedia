-- Prove2me | Theorems.Thm_QEC_QLDPC_detectable_of_card_lt_semanticQuditDistance
-- name    : QEC.QLDPC.detectable_of_card_lt_semanticQuditDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:52:26.74922+00:00
-- url     : https://prove2.me/theorems/e1a3ee52-aa40-43d7-899b-667ae957a3a6
-- title:
--   QLDPC: detectable of card lt semantic Qudit Distance
-- statement:
--   Every operator on a region smaller than semantic distance is detectable.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L70-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L70-L82

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
set_option autoImplicit false
noncomputable section
open QEC
open QEC.QLDPC
universe u v

theorem QEC.QLDPC.detectable_of_card_lt_semanticQuditDistance
    {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (code : Semantics.QuantumCode (Semantics.Qudit.QuditRegister q))
    (region : Semantics.QuditSubsystem q)
    (hcard : Fintype.card region.SelectedCoordinates <
      semanticQuditDistance q code)
    (localOperator : Semantics.Operator region.selectedSystem) :
    Semantics.DetectableOn code
      (region.extendLocalToRegister localOperator) := by sorry
