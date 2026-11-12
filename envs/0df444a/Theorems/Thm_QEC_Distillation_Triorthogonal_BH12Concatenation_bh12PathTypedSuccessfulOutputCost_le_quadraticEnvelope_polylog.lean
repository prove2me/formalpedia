-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathTypedSuccessfulOutputCost_le_quadraticEnvelope_polylog
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathTypedSuccessfulOutputCost_le_quadraticEnvelope_polylog
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:33:18.620436+00:00
-- url     : https://prove2.me/theorems/0d1ef48b-1cc1-4158-8d17-281e136ccb7d
-- title:
--   BH12 Concatenation: bh12 Path Typed Successful Output Cost le quadratic Envelope polylog
-- statement:
--   The actual finite typed BH12 cost is bounded by the real-rpow of the
--   compiled finite quadratic-envelope logarithm, with no target-family or
--   asymptotic packaging.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2573-L2648
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2573-L2648

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathTypedSuccessfulOutputCost_le_quadraticEnvelope_polylog
    (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (hp : 0 < p.rate) (hq : 0 < q) (z : Nat) (path : depthOutputPath q z) :
    bh12PathTypedSuccessfulOutputCost q p hsmall hhalf hstrong z path ≤
      bh12QuadraticEnvelopeCostCoefficient q p *
        Real.rpow (Real.log (1 / bh12QuadraticEnvelope q p z))
          (bh12BlockExponent q) := by sorry
