-- Prove2me | Theorems.Thm_QEC_Distillation_KT19MagicResource_KT19PrimeQuditCSS_nonzeroMass_eq_one_sub_mu_zero
-- name    : QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.nonzeroMass_eq_one_sub_mu_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:50:24.839644+00:00
-- url     : https://prove2.me/theorems/201c5151-97a8-43bc-adf8-8d2305d7af28
-- title:
--   KT19 Prime Qudit CSS: nonzero Mass eq one sub mu zero
-- statement:
--   For a normalized one-site distribution, the total nonzero-label mass is
--   exactly the complement of its zero-label mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/MagicResource.lean#L842-L858
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/MagicResource.lean#L842-L858

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

theorem QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.nonzeroMass_eq_one_sub_mu_zero (mu : ZMod p → ℝ)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) :
    nonzeroMass p mu = 1 - mu 0 := by sorry
