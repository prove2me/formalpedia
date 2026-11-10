-- Prove2me | Theorems.Thm_QEC_Distillation_KT19MagicResource_KT19PrimeQuditCSS_magicRegisterKrausFamily_complete
-- name    : QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.magicRegisterKrausFamily_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:49:14.789897+00:00
-- url     : https://prove2.me/theorems/fc764fec-981b-4978-a958-d7223397aaf8
-- title:
--   KT19 Prime Qudit CSS: magic Register Kraus Family complete
-- statement:
--   The KT19 Prime Qudit CSS construction uses the magic Register Kraus Family complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/MagicResource.lean#L778-L785
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/MagicResource.lean#L778-L785

import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_MagicResource
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19MagicResource
open Semantics
open QEC.Distillation.KT19PrimeQuditCSS
open scoped BigOperators
open QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
universe u v w
variable (p : Nat) [NeZero p]
variable {Site : Type u} [Fintype Site]
attribute [local instance] QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS._p2m_local_instance_d135975d44_41
attribute [local instance] QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.primeQuditRegisterLabelFintypeLocal

theorem QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.magicRegisterKrausFamily_complete :
    (magicRegisterKrausFamily p (Site := Site)).Complete := by sorry
