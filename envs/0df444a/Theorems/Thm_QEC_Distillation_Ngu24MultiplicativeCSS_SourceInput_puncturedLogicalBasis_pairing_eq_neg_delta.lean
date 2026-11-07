-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_puncturedLogicalBasis_pairing_eq_neg_delta
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.puncturedLogicalBasis_pairing_eq_neg_delta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:11:10.163839+00:00
-- url     : https://prove2.me/theorems/5492302e-5cf9-4901-ad9c-f56e4a4967bb
-- title:
--   Source Input: punctured Logical Basis pairing eq neg delta
-- statement:
--   Logical basis representatives have the exact negative Kronecker pairing over any field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CSSShortening.lean#L622-L632
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CSSShortening.lean#L622-L632

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

theorem QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.puncturedLogicalBasis_pairing_eq_neg_delta (data : SourceInput F I Logical)
    (a b : Logical) :
    wordPairing (data.puncturedLogicalWord (canonicalBasisWord a))
      (data.puncturedLogicalWord (canonicalBasisWord b)) =
        -(if a = b then 1 else 0) := by sorry
