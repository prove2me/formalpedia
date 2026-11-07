-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_puncturedLogicalWord_pairing_eq_neg
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.puncturedLogicalWord_pairing_eq_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:45:42.0472+00:00
-- url     : https://prove2.me/theorems/18022dad-bb9f-41b3-baac-be0b300306b4
-- title:
--   Source Input: punctured Logical Word pairing eq neg
-- statement:
--   Punctured systematic representatives have the negative logical pairing over any field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CSSShortening.lean#L593-L605
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CSSShortening.lean#L593-L605

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

theorem QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.puncturedLogicalWord_pairing_eq_neg (data : SourceInput F I Logical)
    (u v : Word F Logical) :
    wordPairing (data.puncturedLogicalWord u) (data.puncturedLogicalWord v) =
      -wordPairing u v := by sorry
