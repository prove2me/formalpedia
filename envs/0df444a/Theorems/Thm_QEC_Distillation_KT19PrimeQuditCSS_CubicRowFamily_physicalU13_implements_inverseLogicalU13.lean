-- Prove2me | Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_CubicRowFamily_physicalU13_implements_inverseLogicalU13
-- name    : QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily.physicalU13_implements_inverseLogicalU13
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:44:44.424497+00:00
-- url     : https://prove2.me/theorems/ab591912-c63a-458d-bc17-5528dda9b5ef
-- title:
--   Cubic Row Family: physical U13 implements inverse Logical U13
-- statement:
--   The p>=5 KT19 route exports the full semantic encoder-commuting predicate.
--
--   The cubic row algebra is intentionally stated at its natural `NeZero p`
--   generality.  This wrapper binds the reusable physical-to-inverse-logical API
--   to the prime, nondegenerate cubic hierarchy established by
--   `u13_has_hierarchy`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L1208-L1216
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L1208-L1216

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
open QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily
variable {p : Nat} [NeZero p] {Logical Stabilizer Site : Type u}
variable [Fintype Logical] [Fintype Stabilizer] [Fintype Site] [DecidableEq Site]

theorem QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily.physicalU13_implements_inverseLogicalU13 (R : CubicRowFamily p Logical Stabilizer Site)
    (hp : PrimeAtLeastFive p) :
    R.encodedCode.ImplementsLogicalGate R.physicalU13 R.logicalInverseU13 := by sorry
