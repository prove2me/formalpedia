-- Prove2me | Theorems.Thm_QEC_QLDPC_semanticQuditDistance_le_of_nondetectable
-- name    : QEC.QLDPC.semanticQuditDistance_le_of_nondetectable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:52:26.681317+00:00
-- url     : https://prove2.me/theorems/4a28ee4a-ab6c-47af-969c-a6bf2c91ce2f
-- title:
--   QLDPC: semantic Qudit Distance le of nondetectable
-- statement:
--   Any concrete nondetectable local operator upper-bounds semantic distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L58-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L58-L67

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
set_option autoImplicit false
noncomputable section
open QEC
open QEC.QLDPC
universe u v

theorem QEC.QLDPC.semanticQuditDistance_le_of_nondetectable
    {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (code : Semantics.QuantumCode (Semantics.Qudit.QuditRegister q))
    (region : Semantics.QuditSubsystem q)
    (localOperator : Semantics.Operator region.selectedSystem)
    (hoperator : ¬ Semantics.DetectableOn code
      (region.extendLocalToRegister localOperator)) :
    semanticQuditDistance q code ≤ Fintype.card region.SelectedCoordinates := by sorry
