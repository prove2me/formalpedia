-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12TwoPow_mul_quadraticEnvelopeLogGrowthBase_le_log
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12TwoPow_mul_quadraticEnvelopeLogGrowthBase_le_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:31:45.747768+00:00
-- url     : https://prove2.me/theorems/07e4f10a-7d76-4523-a2c7-4118347f9a28
-- title:
--   BH12 Concatenation: bh12 Two Pow mul quadratic Envelope Log Growth Base le log
-- statement:
--   The compiled finite closed form gives the source-faithful logarithmic
--   lower bound for every finite quadratic-envelope depth.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1814-L1846
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1814-L1846

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12TwoPow_mul_quadraticEnvelopeLogGrowthBase_le_log
    (q : Nat) (p : ErrorParameter)
    (hp : 0 < p.rate) (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2) (z : Nat) :
    (2 : ℝ) ^ z * bh12QuadraticEnvelopeLogGrowthBase q p ≤
      Real.log (1 / bh12QuadraticEnvelope q p z) := by sorry
