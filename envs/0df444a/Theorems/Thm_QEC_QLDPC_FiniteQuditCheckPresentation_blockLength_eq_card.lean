-- Prove2me | Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_blockLength_eq_card
-- name    : QEC.QLDPC.FiniteQuditCheckPresentation.blockLength_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:52:12.836373+00:00
-- url     : https://prove2.me/theorems/189908ea-1531-4004-ad88-97629b8f785f
-- title:
--   Finite Qudit Check Presentation: block Length eq card
-- statement:
--   The derived block length is the physical coordinate cardinality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L229-L231
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L229-L231

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

theorem QEC.QLDPC.FiniteQuditCheckPresentation.blockLength_eq_card (P : FiniteQuditCheckPresentation ι κ) :
    P.blockLength = Fintype.card ι := by sorry

attribute [defeq] QEC.QLDPC.FiniteQuditCheckPresentation.blockLength_eq_card
