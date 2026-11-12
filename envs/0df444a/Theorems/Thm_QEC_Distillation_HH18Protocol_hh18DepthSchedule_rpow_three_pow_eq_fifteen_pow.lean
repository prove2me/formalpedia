-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthSchedule_rpow_three_pow_eq_fifteen_pow
-- name    : QEC.Distillation.HH18Protocol.hh18DepthSchedule_rpow_three_pow_eq_fifteen_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:49:02.640846+00:00
-- url     : https://prove2.me/theorems/4e4d0f2c-c7b3-44ce-9a75-af44aa9beeb3
-- title:
--   HH18 Protocol: hh18 Depth Schedule rpow three pow eq fifteen pow
-- statement:
--   The real-power form of the fixed cubic exponent is exactly the literal
--   fifteen-to-one slot ratio at every finite depth.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1353-L1372
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1353-L1372

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
universe u
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instProtocolClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Protocol.instProtocolClassicalDecidable
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
open OneQubitMagic

theorem QEC.Distillation.HH18Protocol.hh18DepthSchedule_rpow_three_pow_eq_fifteen_pow (depth : Nat) :
    Real.rpow ((3 : ℝ) ^ depth) hh18DepthScheduleGamma =
      (15 : ℝ) ^ depth := by sorry
