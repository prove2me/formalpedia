-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_puncturedLogicalWord_pairing_puncture_one_eq_sum_of_char_two
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.puncturedLogicalWord_pairing_puncture_one_eq_sum_of_char_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:11:19.630825+00:00
-- url     : https://prove2.me/theorems/70ef51c4-4c58-4670-9d7b-02fac5261672
-- title:
--   Source Input: punctured Logical Word pairing puncture one eq sum of char two
-- statement:
--   Characteristic two changes the preceding negative coordinate sum to the source's positive form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CSSShortening.lean#L663-L668
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CSSShortening.lean#L663-L668

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

theorem QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.puncturedLogicalWord_pairing_puncture_one_eq_sum_of_char_two
    (data : SourceInput F I Logical) [CharP F 2] (u : Word F Logical) :
    wordPairing (data.puncturedLogicalWord u) (data.puncture (1 : Word F I)) =
      ∑ a : Logical, u a := by sorry
