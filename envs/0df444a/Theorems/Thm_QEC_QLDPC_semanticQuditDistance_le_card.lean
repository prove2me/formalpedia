-- Prove2me | Theorems.Thm_QEC_QLDPC_semanticQuditDistance_le_card
-- name    : QEC.QLDPC.semanticQuditDistance_le_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:53:26.792636+00:00
-- url     : https://prove2.me/theorems/d3a40f3b-619d-475b-94b9-05ed68e8eb73
-- title:
--   QLDPC: semantic Qudit Distance le card
-- statement:
--   Semantic distance never exceeds the number of physical coordinates,
--   including the convention that a code with no nondetectable operator has distance zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L98-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L98-L113

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
set_option autoImplicit false
noncomputable section
open QEC
open QEC.QLDPC
universe u v

theorem QEC.QLDPC.semanticQuditDistance_le_card
    {ι : Type u} [Fintype ι] [DecidableEq ι] (q : ι → Nat)
    (code : Semantics.QuantumCode (Semantics.Qudit.QuditRegister q)) :
    semanticQuditDistance q code ≤ Fintype.card ι := by sorry
