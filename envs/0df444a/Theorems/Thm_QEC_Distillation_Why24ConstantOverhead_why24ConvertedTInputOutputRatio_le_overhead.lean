-- Prove2me | Theorems.Thm_QEC_Distillation_Why24ConstantOverhead_why24ConvertedTInputOutputRatio_le_overhead
-- name    : QEC.Distillation.Why24ConstantOverhead.why24ConvertedTInputOutputRatio_le_overhead
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:45:46.417606+00:00
-- url     : https://prove2.me/theorems/c97ea26e-2034-4fb6-a6ac-5f3f91f66c6d
-- title:
--   Why24 Constant Overhead: why24 Converted TInput Output Ratio le overhead
-- statement:
--   After both finite conversions, `B` actual WHY24 blocks use at most `3360`
--   non-seed noisy T resources per fresh T output.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/Distillation/ConstantOverhead.lean#L216-L237
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/Distillation/ConstantOverhead.lean#L216-L237

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

theorem QEC.Distillation.Why24ConstantOverhead.why24ConvertedTInputOutputRatio_le_overhead (index batch : Nat)
    (hbatch : 0 < batch) :
    ((4 * batch * why24OneRoundInputCount index : Nat) : Real) /
        (2 * batch * why24OneRoundOutputCount index) <= 3360 := by sorry
