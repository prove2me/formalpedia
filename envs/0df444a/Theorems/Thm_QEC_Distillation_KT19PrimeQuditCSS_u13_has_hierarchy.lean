-- Prove2me | Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_u13_has_hierarchy
-- name    : QEC.Distillation.KT19PrimeQuditCSS.u13_has_hierarchy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:41:57.766393+00:00
-- url     : https://prove2.me/theorems/6ccdfb81-c4e4-42dd-a47c-627581ae2d67
-- title:
--   KT19 Prime Qudit CSS: u13 has hierarchy
-- statement:
--   The p>=5 route has a concrete cubic-to-quadratic-to-Pauli hierarchy witness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L416-L420
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L416-L420

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

theorem QEC.Distillation.KT19PrimeQuditCSS.u13_has_hierarchy (p : Nat) [NeZero p] (hp : PrimeAtLeastFive p) :
    U13HierarchyWitness p := by sorry
