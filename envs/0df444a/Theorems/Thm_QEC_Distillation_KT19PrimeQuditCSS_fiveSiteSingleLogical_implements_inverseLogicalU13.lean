-- Prove2me | Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_fiveSiteSingleLogical_implements_inverseLogicalU13
-- name    : QEC.Distillation.KT19PrimeQuditCSS.fiveSiteSingleLogical_implements_inverseLogicalU13
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:45:03.026606+00:00
-- url     : https://prove2.me/theorems/51b7fdf1-f853-48f8-b548-86b46125510f
-- title:
--   KT19 Prime Qudit CSS: five Site Single Logical implements inverse Logical U13
-- statement:
--   The p=5 fixture satisfies the semantic implementation predicate, not merely basis preservation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L1312-L1316
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L1312-L1316

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

theorem QEC.Distillation.KT19PrimeQuditCSS.fiveSiteSingleLogical_implements_inverseLogicalU13 :
    fiveSiteSingleLogical.encodedCode.ImplementsLogicalGate fiveSiteSingleLogical.physicalU13
      fiveSiteSingleLogical.logicalInverseU13 := by sorry
