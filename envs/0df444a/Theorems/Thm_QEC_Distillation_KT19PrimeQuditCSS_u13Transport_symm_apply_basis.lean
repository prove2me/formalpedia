-- Prove2me | Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_u13Transport_symm_apply_basis
-- name    : QEC.Distillation.KT19PrimeQuditCSS.u13Transport_symm_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:41:42.037236+00:00
-- url     : https://prove2.me/theorems/df037de6-593b-4be0-a78d-dfa1db784106
-- title:
--   KT19 Prime Qudit CSS: u13 Transport symm apply basis
-- statement:
--   The inverse cubic transport has the negative cubic phase on a basis ket.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L261-L270
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L261-L270

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

theorem QEC.Distillation.KT19PrimeQuditCSS.u13Transport_symm_apply_basis (p : Nat) [NeZero p] (x : ZMod p) :
    (u13Transport p).symm (quditBasisKet p x) =
      phase p (-(x ^ 3)) • quditBasisKet p x := by sorry
