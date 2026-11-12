-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathUniformPhysicalTarget
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathUniformPhysicalTarget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:32:04.067059+00:00
-- url     : https://prove2.me/theorems/dc5a3041-edd9-4b71-9370-d0118453cd52
-- title:
--   BH12 Concatenation: bh12 Path Uniform Physical Target
-- statement:
--   At one finite uniform target depth, every physical path has positive
--   actual success, exact transported selected-port density, and the requested
--   rate bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1924-L1950
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1924-L1950

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathUniformPhysicalTarget (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hquadraticSmall : quadraticCoefficient q * p.rate ≤ 1)
    (hstrict : quadraticCoefficient q * p.rate < 1)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ z : Nat, ∀ path : depthOutputPath q z,
      0 < rawSuccessMass q (bh12PathParameter q p z path) ∧
        0 < (bh12PathRun q p z path).successProbability ∧
          (∀ port : OddRow q,
            bh12PathSelectedPortTransportedDensity q p z path port =
              OneQubit.diagonalAResource
                (bh12TotalNextParameter q (bh12PathParameter q p z path) port)) ∧
            (bh12PathParameter q p z path).rate ≤ epsilon := by sorry
