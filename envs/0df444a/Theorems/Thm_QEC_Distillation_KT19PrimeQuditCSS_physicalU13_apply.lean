-- Prove2me | Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_physicalU13_apply
-- name    : QEC.Distillation.KT19PrimeQuditCSS.physicalU13_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:41:37.985068+00:00
-- url     : https://prove2.me/theorems/fc66e48c-70f9-4c00-be64-2780713a910a
-- title:
--   KT19 Prime Qudit CSS: physical U13 apply
-- statement:
--   The physical tensor product has the product of the literal local cubic phases.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L507-L524
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L507-L524

import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19PrimeQuditCSS
open Semantics
open scoped BigOperators
universe u
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
attribute [local instance] primeQuditRegisterLabelFintype

theorem QEC.Distillation.KT19PrimeQuditCSS.physicalU13_apply (p : Nat) [NeZero p] {Site : Type u}
    [Fintype Site] [DecidableEq Site]
    (psi : PrimeQuditRegister p Site) (label : PrimeQuditRegisterLabel p Site) :
    physicalU13 p psi label =
      (∏ site : Site, u13AtAmplitude p site label) * psi label := by sorry
