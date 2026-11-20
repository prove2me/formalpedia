-- Prove2me | Theorems.Thm_QEC_Distillation_Why24ConstantOverhead_why24InputOutputRatio_le_overhead
-- name    : QEC.Distillation.Why24ConstantOverhead.why24InputOutputRatio_le_overhead
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:45:30.613382+00:00
-- url     : https://prove2.me/theorems/09accacd-bf23-4f5b-b7ff-91bd0d9ec871
-- title:
--   Why24 Constant Overhead: why24 Input Output Ratio le overhead
-- statement:
--   The actual one-round `70 n / k` resource ratio is uniformly at most
--   `1680`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/Distillation/ConstantOverhead.lean#L197-L212
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/Distillation/ConstantOverhead.lean#L197-L212

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

theorem QEC.Distillation.Why24ConstantOverhead.why24InputOutputRatio_le_overhead (index : Nat) :
    (why24OneRoundInputCount index : Real) /
        why24OneRoundOutputCount index <= why24OverheadConstant := by sorry
