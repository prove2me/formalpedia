-- Prove2me | Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_physicalU13_apply_basis_phase
-- name    : QEC.Distillation.KT19PrimeQuditCSS.physicalU13_apply_basis_phase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:42:09.103038+00:00
-- url     : https://prove2.me/theorems/f1a2d8ca-2359-43ef-91ae-bfd6e7b7adad
-- title:
--   KT19 Prime Qudit CSS: physical U13 apply basis phase
-- statement:
--   The physical product has its cubic-exponent phase on every computational ket.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L554-L563
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L554-L563

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

theorem QEC.Distillation.KT19PrimeQuditCSS.physicalU13_apply_basis_phase (p : Nat) [NeZero p] {Site : Type u}
    [Fintype Site] [DecidableEq Site] (label : PrimeQuditRegisterLabel p Site) :
    physicalU13 p (registerBasisKet p label) =
      phase p (cubicExponent p label) • registerBasisKet p label := by sorry
