-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathSelectedPortTransportedDensity_eq_diagonalAResource
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathSelectedPortTransportedDensity_eq_diagonalAResource
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:27:21.659428+00:00
-- url     : https://prove2.me/theorems/57d2790d-86b0-4ed5-a60a-fdc785306af3
-- title:
--   BH12 Concatenation: bh12 Path Selected Port Transported Density eq diagonal AResource
-- statement:
--   The finite-path physical selected output is exactly the diagonal A-basis
--   resource at its total next parameter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1628-L1643
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1628-L1643

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathSelectedPortTransportedDensity_eq_diagonalAResource
    (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hquadraticSmall : quadraticCoefficient q * p.rate ≤ 1)
    (z : Nat) (path : depthOutputPath q z) (port : OddRow q) :
    bh12PathSelectedPortTransportedDensity q p z path port =
      OneQubit.diagonalAResource
        (bh12TotalNextParameter q (bh12PathParameter q p z path) port) := by sorry
