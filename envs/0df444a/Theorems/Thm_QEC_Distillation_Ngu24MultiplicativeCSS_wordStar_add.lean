-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_wordStar_add
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.wordStar_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:10:32.57513+00:00
-- url     : https://prove2.me/theorems/00db6b0d-f2b9-4ab8-825c-353ed75eead8
-- title:
--   Ngu24 Multiplicative CSS: word Star add
-- statement:
--   The Ngu24 Multiplicative CSS construction uses the word Star add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CSSShortening.lean#L45-L48
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CSSShortening.lean#L45-L48

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
omit [Fintype F] [Fintype I]

theorem QEC.Distillation.Ngu24MultiplicativeCSS.wordStar_add (x y z : Word F I) :
    wordStar (x + y) z = wordStar x z + wordStar y z := by sorry
