-- Prove2me | Theorems.Thm_QEC_QLDPC_semanticQuditDistance_attained
-- name    : QEC.QLDPC.semanticQuditDistance_attained
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:52:18.084383+00:00
-- url     : https://prove2.me/theorems/b8143b23-d2f3-4296-ada5-a3abfe05c61a
-- title:
--   QLDPC: semantic Qudit Distance attained
-- statement:
--   A nonempty logical-region set attains the finite semantic distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L85-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L85-L94

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
set_option autoImplicit false
noncomputable section
open QEC
open QEC.QLDPC
universe u v

theorem QEC.QLDPC.semanticQuditDistance_attained
    {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (code : Semantics.QuantumCode (Semantics.Qudit.QuditRegister q))
    (hnonempty : {weight : Nat | ∃ region : Semantics.QuditSubsystem q,
      Fintype.card region.SelectedCoordinates = weight ∧
        SupportsNondetectableLocalOperator code region}.Nonempty) :
    ∃ region : Semantics.QuditSubsystem q,
      Fintype.card region.SelectedCoordinates = semanticQuditDistance q code ∧
        SupportsNondetectableLocalOperator code region := by sorry
