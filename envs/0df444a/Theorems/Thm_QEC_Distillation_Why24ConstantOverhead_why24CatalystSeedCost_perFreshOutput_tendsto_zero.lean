-- Prove2me | Theorems.Thm_QEC_Distillation_Why24ConstantOverhead_why24CatalystSeedCost_perFreshOutput_tendsto_zero
-- name    : QEC.Distillation.Why24ConstantOverhead.why24CatalystSeedCost_perFreshOutput_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:50:46.528926+00:00
-- url     : https://prove2.me/theorems/cd357fa7-dea7-45b6-90ef-7bd1a75eab23
-- title:
--   Why24 Constant Overhead: why24 Catalyst Seed Cost per Fresh Output tendsto zero
-- statement:
--   A physical catalyst is never assigned zero cost; only its positive finite
--   BH12 cost is amortized over a growing number of fresh outputs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/Distillation/ConstantOverhead.lean#L361-L364
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/Distillation/ConstantOverhead.lean#L361-L364

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

theorem QEC.Distillation.Why24ConstantOverhead.why24CatalystSeedCost_perFreshOutput_tendsto_zero :
    Tendsto why24CatalystSeedCostPerFreshOutput atTop (nhds 0) := by sorry
