-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_encodingLinearMap_apply_logical_basis
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.encodingLinearMap_apply_logical_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:45:41.750203+00:00
-- url     : https://prove2.me/theorems/dd4a8b70-1d1e-4e5b-a468-f74d9db34f56
-- title:
--   Source Input: encoding Linear Map apply logical basis
-- statement:
--   On a logical computational basis ket, the encoder is the stated shortened coset ket.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CSSShortening.lean#L508-L513
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CSSShortening.lean#L508-L513

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

theorem QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.encodingLinearMap_apply_logical_basis (data : SourceInput F I Logical)
    (u : Word F Logical) :
    data.encodingLinearMap (registerBasisKet u) = data.shortenedCosetKet u := by sorry
