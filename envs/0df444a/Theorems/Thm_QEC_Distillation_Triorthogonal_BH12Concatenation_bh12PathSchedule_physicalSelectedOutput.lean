-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathSchedule_physicalSelectedOutput
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathSchedule_physicalSelectedOutput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:43:55.750866+00:00
-- url     : https://prove2.me/theorems/08e52172-f39b-4d89-a822-a1b90d57dfee
-- title:
--   BH12 Concatenation: bh12 Path Schedule physical Selected Output
-- statement:
--   The selected final physical output of a nonzero schedule depth has its
--   exact transported density and its same-path actual error is bounded by the
--   compiled target, without an independence assertion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2752-L2770
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2752-L2770

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathSchedule_physicalSelectedOutput (q : Nat)
    (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (z : Nat) (path : depthOutputPath q (z + 1)) :
    (bh12PathParameter q p (z + 1) path).rate ≤
        bh12PathScheduleTargetError q p
          (bh12PathScheduleIndex_succ q z path) ∧
      bh12PathSelectedPortTransportedDensity q p z
          (depthOutputPathPrefix q z path) (depthOutputPathLast q z path) =
        OneQubit.diagonalAResource
          (bh12PathParameter q p (z + 1) path) := by sorry
