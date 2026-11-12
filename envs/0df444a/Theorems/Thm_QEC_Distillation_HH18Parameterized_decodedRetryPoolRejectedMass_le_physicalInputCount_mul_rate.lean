-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolRejectedMass_le_physicalInputCount_mul_rate
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolRejectedMass_le_physicalInputCount_mul_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:09:50.412858+00:00
-- url     : https://prove2.me/theorems/74f036f7-177c-4d3f-84e7-ebbe4141d27c
-- title:
--   HH18 Parameterized: decoded Retry Pool Rejected Mass le physical Input Count mul rate
-- statement:
--   The actual rejected one-block mass is bounded by the physical input count
--   times the supplied diagonal rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/DyadicSlack.lean#L152-L166
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/DyadicSlack.lean#L152-L166

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_FirstMoment
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SuccessResidual
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_DyadicSlack
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instDecodedRetryPoolDyadicSlackClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolRejectedMass_le_physicalInputCount_mul_rate
    {w r m : Nat} (h : Admissible w r m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    1 - acceptedBernoulliMass w r m epsilon ≤
      (physicalInputCount m w : ℝ) * epsilon.1 := by sorry
