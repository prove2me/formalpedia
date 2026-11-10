-- Prove2me | Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_u13_conjugates_x_on_basis
-- name    : QEC.Distillation.KT19PrimeQuditCSS.u13_conjugates_x_on_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:43:44.580295+00:00
-- url     : https://prove2.me/theorems/03f97ecc-1a16-4287-acda-cd05b978e48c
-- title:
--   KT19 Prime Qudit CSS: u13 conjugates x on basis
-- statement:
--   The explicit third-level conjugation identity used by the prime-qudit route.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L423-L436
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L423-L436

import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19PrimeQuditCSS
open Semantics
open scoped BigOperators
universe u
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype

theorem QEC.Distillation.KT19PrimeQuditCSS.u13_conjugates_x_on_basis (p : Nat) [NeZero p]
    (hp : PrimeAtLeastFive p) (x : ZMod p) :
    u13Transport p (xTransport p ((u13Transport p).symm (quditBasisKet p x))) =
      u13ConjugatedXAmplitude p x • quditBasisKet p (x + 1) := by sorry
