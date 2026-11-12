-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathTypedInputSlot_card
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathTypedInputSlot_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:26:16.570771+00:00
-- url     : https://prove2.me/theorems/4fd9d6f0-b4cb-4819-bc66-9b3299ef755a
-- title:
--   BH12 Concatenation: bh12 Path Typed Input Slot card
-- statement:
--   The typed finite raw-input slot count along a BH12 path is exactly the
--   literal one-block input count raised to the path depth.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2469-L2471
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2469-L2471

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily
open BH12NoisyInjection
open BH12Protocol
open Filter Topology

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathTypedInputSlot_card (q z : Nat) :
    Fintype.card (depthRawInputPath q z) = (bh12InputCount q) ^ z := by sorry
