-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_smul_wordStar
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.smul_wordStar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:10:30.972117+00:00
-- url     : https://prove2.me/theorems/603f1568-08b5-4e59-bacc-6832cb54f68b
-- title:
--   Ngu24 Multiplicative CSS: smul word Star
-- statement:
--   The Ngu24 Multiplicative CSS construction uses the smul word Star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CSSShortening.lean#L57-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CSSShortening.lean#L57-L60

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

theorem QEC.Distillation.Ngu24MultiplicativeCSS.smul_wordStar (a : F) (x y : Word F I) :
    a • wordStar x y = wordStar (a • x) y := by sorry
