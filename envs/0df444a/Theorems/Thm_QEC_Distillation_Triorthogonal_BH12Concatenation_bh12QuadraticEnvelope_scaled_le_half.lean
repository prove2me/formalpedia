-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12QuadraticEnvelope_scaled_le_half
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12QuadraticEnvelope_scaled_le_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:31:44.599527+00:00
-- url     : https://prove2.me/theorems/0129acd1-2024-426f-a111-57176a67dc6e
-- title:
--   BH12 Concatenation: bh12 Quadratic Envelope scaled le half
-- statement:
--   Under the strong source-domain coefficient condition, the scaled envelope
--   stays at most one half at every finite depth.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1746-L1765
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1746-L1765

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12QuadraticEnvelope_scaled_le_half (q : Nat) (p : ErrorParameter)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2) :
    ∀ z : Nat,
      quadraticCoefficient q * bh12QuadraticEnvelope q p z ≤ 1 / 2 := by sorry
