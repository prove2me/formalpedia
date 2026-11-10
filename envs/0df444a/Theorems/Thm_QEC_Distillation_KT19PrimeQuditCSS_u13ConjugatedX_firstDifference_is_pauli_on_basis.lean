-- Prove2me | Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_u13ConjugatedX_firstDifference_is_pauli_on_basis
-- name    : QEC.Distillation.KT19PrimeQuditCSS.u13ConjugatedX_firstDifference_is_pauli_on_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:41:46.848936+00:00
-- url     : https://prove2.me/theorems/b1b60a2f-29c2-40b1-8ed3-3211b429a8ea
-- title:
--   KT19 Prime Qudit CSS: u13 Conjugated X first Difference is pauli on basis
-- statement:
--   The linear finite difference acts as a global phase times the actual Pauli Z power.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L393-L399
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L393-L399

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

theorem QEC.Distillation.KT19PrimeQuditCSS.u13ConjugatedX_firstDifference_is_pauli_on_basis (p : Nat) [NeZero p]
    (x : ZMod p) :
    phase p (u13ConjugatedXExponent p (x + 1) - u13ConjugatedXExponent p x) •
        quditBasisKet p x =
      phase p 6 • zPowerTransport p 6 (quditBasisKet p x) := by sorry
