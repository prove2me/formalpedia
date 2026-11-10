-- Prove2me | Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_physicalU13_apply_basis
-- name    : QEC.Distillation.KT19PrimeQuditCSS.physicalU13_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:43:36.825777+00:00
-- url     : https://prove2.me/theorems/8428270d-b288-4068-aff2-914047b92123
-- title:
--   KT19 Prime Qudit CSS: physical U13 apply basis
-- statement:
--   The physical product has the stated cubic action on every register basis ket.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L527-L536
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L527-L536

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

theorem QEC.Distillation.KT19PrimeQuditCSS.physicalU13_apply_basis (p : Nat) [NeZero p] {Site : Type u}
    [Fintype Site] [DecidableEq Site] (label : PrimeQuditRegisterLabel p Site) :
    physicalU13 p (registerBasisKet p label) =
      (∏ site : Site, u13AtAmplitude p site label) • registerBasisKet p label := by sorry
