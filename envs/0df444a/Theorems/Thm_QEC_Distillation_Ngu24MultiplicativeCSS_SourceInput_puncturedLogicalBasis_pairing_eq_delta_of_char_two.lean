-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_puncturedLogicalBasis_pairing_eq_delta_of_char_two
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.puncturedLogicalBasis_pairing_eq_delta_of_char_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:11:08.076203+00:00
-- url     : https://prove2.me/theorems/61ee529d-3ce3-4d8d-964d-d284ad60474e
-- title:
--   Source Input: punctured Logical Basis pairing eq delta of char two
-- statement:
--   The logical-basis pairing has the source's positive delta form in characteristic two.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CSSShortening.lean#L635-L645
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CSSShortening.lean#L635-L645

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

theorem QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.puncturedLogicalBasis_pairing_eq_delta_of_char_two (data : SourceInput F I Logical)
    [CharP F 2] (a b : Logical) :
    wordPairing (data.puncturedLogicalWord (canonicalBasisWord a))
      (data.puncturedLogicalWord (canonicalBasisWord b)) =
        if a = b then 1 else 0 := by sorry
