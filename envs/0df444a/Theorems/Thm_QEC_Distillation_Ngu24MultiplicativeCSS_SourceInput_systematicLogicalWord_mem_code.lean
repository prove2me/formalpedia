-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_systematicLogicalWord_mem_code
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.systematicLogicalWord_mem_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:45:31.293933+00:00
-- url     : https://prove2.me/theorems/f5029214-07fa-4bd2-9487-7b4903b0216c
-- title:
--   Source Input: systematic Logical Word mem code
-- statement:
--   Every systematic representative is a codeword.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CSSShortening.lean#L529-L531
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CSSShortening.lean#L529-L531

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CSSShortening
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Semantics
open scoped BigOperators
universe u
variable {F I Logical : Type u} [Field F] [Fintype F] [Fintype I] [Fintype Logical]
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_7d0f4269de_23
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_7d0f4269de_24
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_7d0f4269de_25
open QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput

theorem QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.systematicLogicalWord_mem_code (data : SourceInput F I Logical) (u : Logical → F) :
    data.systematicLogicalWord u ∈ data.code.carrier := by sorry
