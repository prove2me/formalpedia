-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12QuadraticEnvelopeLogGrowthBase_pos
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12QuadraticEnvelopeLogGrowthBase_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:28:40.537054+00:00
-- url     : https://prove2.me/theorems/d39c4762-9c25-4b08-a9ed-25c3e1eadc16
-- title:
--   BH12 Concatenation: bh12 Quadratic Envelope Log Growth Base pos
-- statement:
--   The strong input domain makes the quadratic-envelope logarithmic base
--   strictly positive.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1803-L1810
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1803-L1810

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12QuadraticEnvelopeLogGrowthBase_pos (q : Nat) (p : ErrorParameter)
    (hp : 0 < p.rate) (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2) :
    0 < bh12QuadraticEnvelopeLogGrowthBase q p := by sorry
