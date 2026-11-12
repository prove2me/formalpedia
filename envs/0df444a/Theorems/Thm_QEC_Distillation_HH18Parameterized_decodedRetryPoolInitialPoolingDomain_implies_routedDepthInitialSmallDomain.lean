-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolInitialPoolingDomain_implies_routedDepthInitialSmallDomain
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolInitialPoolingDomain_implies_routedDepthInitialSmallDomain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:40:11.2571+00:00
-- url     : https://prove2.me/theorems/bf8f83eb-f5f7-4806-baaa-9c5e6823ac92
-- title:
--   HH18 Parameterized: decoded Retry Pool Initial Pooling Domain implies routed Depth Initial Small Domain
-- statement:
--   The pooling domain is strictly stronger than the existing quarter-domain
--   used to construct every path-indexed successor rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/SuccessBudget.lean#L36-L48
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/SuccessBudget.lean#L36-L48

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_DyadicSlack
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_SuccessBudget
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding
open Coding.ReedMuller Coding.PuncturedReedMuller
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolInitialPoolingDomain_implies_routedDepthInitialSmallDomain
    {w r m : Nat} (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon) :
    routedDepthInitialSmallDomain w r m epsilon := by sorry
