-- Prove2me | Theorems.Thm_QEC_QLDPC_le_semanticQuditDistance_of_detectable_and_exists_nondetectable
-- name    : QEC.QLDPC.le_semanticQuditDistance_of_detectable_and_exists_nondetectable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:53:44.210637+00:00
-- url     : https://prove2.me/theorems/0ee573b0-52b4-4222-b828-8d7f510c60f0
-- title:
--   QLDPC: le semantic Qudit Distance of detectable and exists nondetectable
-- statement:
--   A detecting threshold lower-bounds semantic distance once some local failure exists.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L116-L136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L116-L136

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
set_option autoImplicit false
noncomputable section
open QEC
open QEC.QLDPC
universe u v

theorem QEC.QLDPC.le_semanticQuditDistance_of_detectable_and_exists_nondetectable
    {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (code : Semantics.QuantumCode (Semantics.Qudit.QuditRegister q))
    (d : Nat)
    (hdetect : ∀ region : Semantics.QuditSubsystem q,
      Fintype.card region.SelectedCoordinates < d →
        ∀ localOperator : Semantics.Operator region.selectedSystem,
          Semantics.DetectableOn code
            (region.extendLocalToRegister localOperator))
    (hexists : ∃ region : Semantics.QuditSubsystem q,
      SupportsNondetectableLocalOperator code region) :
    d ≤ semanticQuditDistance q code := by sorry
