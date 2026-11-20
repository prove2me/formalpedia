-- Prove2me | Theorems.Thm_QEC_Distillation_Why24ConstantOverhead_why24OneRoundOutputError_le_geometric
-- name    : QEC.Distillation.Why24ConstantOverhead.why24OneRoundOutputError_le_geometric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:46:29.341359+00:00
-- url     : https://prove2.me/theorems/8fce2d7c-a8a6-4042-95a0-feb1739d3312
-- title:
--   Why24 Constant Overhead: why24 One Round Output Error le geometric
-- statement:
--   Every actual correlated one-round output below the explicit threshold is
--   bounded by the geometric envelope.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/Distillation/ConstantOverhead.lean#L185-L193
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/Distillation/ConstantOverhead.lean#L185-L193

import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_OneRound
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_ResourceConversions
import Definitions.Def_QEC_Results_Distillation_ConstantOverhead
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Why24ConstantOverhead
open Filter Topology
open Semantics
open Why24AGFamily Why24OneRoundProtocol
open QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
open Triorthogonal.BH12Concatenation
open Triorthogonal.BH12EvenFamily
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12Protocol

theorem QEC.Distillation.Why24ConstantOverhead.why24OneRoundOutputError_le_geometric (index : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount index))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount index)))
    (hthreshold : preparation.rate < why24ThresholdRate) :
    why24OneRoundOutputError index preparation <=
      why24GeometricErrorEnvelope index := by sorry
