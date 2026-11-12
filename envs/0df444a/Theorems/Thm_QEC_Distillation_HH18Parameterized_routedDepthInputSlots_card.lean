-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthInputSlots_card
-- name    : QEC.Distillation.HH18Parameterized.routedDepthInputSlots_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:52:43.600986+00:00
-- url     : https://prove2.me/theorems/69f751a7-a756-4331-b2c5-bef2d825531d
-- title:
--   HH18 Parameterized: routed Depth Input Slots card
-- statement:
--   The exact cardinality of the finite routed physical-input address carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L43-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L43-L46

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_FreshDepth
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
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.routedDepthInputSlots_card (m w depth : Nat) :
    Fintype.card (routedDepthInputSlots m w depth) =
      physicalInputCount m w ^ depth := by sorry
