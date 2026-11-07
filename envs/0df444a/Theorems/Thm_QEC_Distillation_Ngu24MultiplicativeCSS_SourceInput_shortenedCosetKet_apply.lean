-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_shortenedCosetKet_apply
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.shortenedCosetKet_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:10:54.503282+00:00
-- url     : https://prove2.me/theorems/70b525d3-5490-449b-ac8a-c81337745cf4
-- title:
--   Source Input: shortened Coset Ket apply
-- statement:
--   Every summand has exactly the declared uniform amplitude.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CSSShortening.lean#L376-L391
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CSSShortening.lean#L376-L391

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

theorem QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.shortenedCosetKet_apply (data : SourceInput F I Logical) (u : Word F Logical)
    (h : H0 data) :
    inner Complex (registerBasisKet (data.shortenedCosetLabel u h)) (data.shortenedCosetKet u) =
      cosetNormalization (H0 data) := by sorry
