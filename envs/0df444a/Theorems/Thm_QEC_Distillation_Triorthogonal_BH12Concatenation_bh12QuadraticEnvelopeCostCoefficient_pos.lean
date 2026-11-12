-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12QuadraticEnvelopeCostCoefficient_pos
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12QuadraticEnvelopeCostCoefficient_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:31:52.420213+00:00
-- url     : https://prove2.me/theorems/04ccfbf9-0b9a-48fb-93d1-21abd9256228
-- title:
--   BH12 Concatenation: bh12 Quadratic Envelope Cost Coefficient pos
-- statement:
--   On the explicit positive/small-rate domain, the exact finite-depth cost
--   coefficient is positive (and hence nonnegative).
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1857-L1864
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1857-L1864

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12QuadraticEnvelopeCostCoefficient_pos (q : Nat) (p : ErrorParameter)
    (hp : 0 < p.rate) (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2) :
    0 < bh12QuadraticEnvelopeCostCoefficient q p := by sorry
