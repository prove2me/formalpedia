-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_noisyInput_eq_independentNoisyTRegister
-- name    : QEC.Distillation.HH18Parameterized.noisyInput_eq_independentNoisyTRegister
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:35:54.669012+00:00
-- url     : https://prove2.me/theorems/e0ecf48f-885a-4451-93b9-936928b761c4
-- title:
--   HH18 Parameterized: noisy Input eq independent Noisy TRegister
-- statement:
--   The parameterized physical input is the generic independent finite
--   register construction on its actual physical-site type.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Preparation.lean#L75-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Preparation.lean#L75-L80

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Types
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Preparation
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.noisyInput_eq_independentNoisyTRegister
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (m w : Nat) :
    noisyInput epsilon m w =
      HH18NoisyInput.independentNoisyTRegister
        (ι := PhysicalSite m w) epsilon := by sorry
