-- Prove2me | Theorems.Thm_QEC_QLDPC_FiniteQuditCheck_globalOperator_eq_extendLocalToRegister
-- name    : QEC.QLDPC.FiniteQuditCheck.globalOperator_eq_extendLocalToRegister
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:52:14.156206+00:00
-- url     : https://prove2.me/theorems/44f46bd2-9f35-49a4-8c66-507ef7c7492f
-- title:
--   Finite Qudit Check: global Operator eq extend Local To Register
-- statement:
--   The Finite Qudit Check construction uses the global Operator eq extend Local To Register property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L155-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L155-L159

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
set_option autoImplicit false
noncomputable section
open QEC
open QEC.QLDPC
universe u v
open QEC.QLDPC.FiniteQuditCheck
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {alphabetSize : Nat}

theorem QEC.QLDPC.FiniteQuditCheck.globalOperator_eq_extendLocalToRegister
    (check : FiniteQuditCheck ι alphabetSize) :
    check.globalOperator =
      check.region.extendLocalToRegister check.localOperator := by sorry

attribute [defeq] QEC.QLDPC.FiniteQuditCheck.globalOperator_eq_extendLocalToRegister
