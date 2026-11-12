-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_allZeroErrorWordWeight
-- name    : QEC.Distillation.HH18Parameterized.allZeroErrorWordWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:01:40.553482+00:00
-- url     : https://prove2.me/theorems/f02018ef-7611-42a9-9dee-6089d6e1fe62
-- title:
--   HH18 Parameterized: all Zero Error Word Weight
-- statement:
--   The all-zero physical error word has its literal product Bernoulli mass
--   over the actual parameterized physical input carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SuccessResidual.lean#L32-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SuccessResidual.lean#L32-L37

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SuccessResidual
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instSuccessClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.allZeroErrorWordWeight (m w : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    HH18NoisyInput.errorWordWeight epsilon (0 : PhysicalErrorWord m w) =
      (1 - epsilon.1) ^ physicalInputCount m w := by sorry
