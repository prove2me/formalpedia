-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_puncturedLogicalBasis_pairing_puncture_one_eq_one_of_char_two
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.puncturedLogicalBasis_pairing_puncture_one_eq_one_of_char_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:11:28.075315+00:00
-- url     : https://prove2.me/theorems/cc0f66ab-0ea0-4ff0-8e9f-c57f06fdcd58
-- title:
--   Source Input: punctured Logical Basis pairing puncture one eq one of char two
-- statement:
--   In characteristic two, the all-ones pairing of a logical basis representative is one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CSSShortening.lean#L679-L684
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CSSShortening.lean#L679-L684

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

theorem QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.puncturedLogicalBasis_pairing_puncture_one_eq_one_of_char_two
    (data : SourceInput F I Logical) [CharP F 2] (a : Logical) :
    wordPairing (data.puncturedLogicalWord (canonicalBasisWord a))
      (data.puncture (1 : Word F I)) = 1 := by sorry
