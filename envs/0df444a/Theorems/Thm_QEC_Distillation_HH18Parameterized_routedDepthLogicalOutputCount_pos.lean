-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthLogicalOutputCount_pos
-- name    : QEC.Distillation.HH18Parameterized.routedDepthLogicalOutputCount_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:37:49.951448+00:00
-- url     : https://prove2.me/theorems/29313622-632a-4b81-b9be-4a53cc99081f
-- title:
--   HH18 Parameterized: routed Depth Logical Output Count pos
-- statement:
--   The parameterized logical output count is positive, as follows from the
--   all-zero logical address and the exact depth-one output-slot cardinality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L396-L400
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L396-L400

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
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

theorem QEC.Distillation.HH18Parameterized.routedDepthLogicalOutputCount_pos (m w : Nat) :
    0 < logicalOutputCount m w := by sorry
