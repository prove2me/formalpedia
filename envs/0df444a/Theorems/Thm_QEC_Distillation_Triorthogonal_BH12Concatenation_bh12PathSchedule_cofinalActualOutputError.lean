-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathSchedule_cofinalActualOutputError
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathSchedule_cofinalActualOutputError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:29:58.852092+00:00
-- url     : https://prove2.me/theorems/08f91e01-a63f-4845-ad55-65e7f1f4a4b9
-- title:
--   BH12 Concatenation: bh12 Path Schedule cofinal Actual Output Error
-- statement:
--   The actual BH12 paths are cofinal in positive error targets.  This is a
--   direct reuse of the compiled finite-target physical theorem, not a second
--   convergence proof.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2817-L2832
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2817-L2832

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathSchedule_cofinalActualOutputError (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ z : Nat, ∀ path : depthOutputPath q z,
      0 < rawSuccessMass q (bh12PathParameter q p z path) ∧
        0 < (bh12PathRun q p z path).successProbability ∧
          (∀ port : OddRow q,
            bh12PathSelectedPortTransportedDensity q p z path port =
              OneQubit.diagonalAResource
                (bh12TotalNextParameter q (bh12PathParameter q p z path) port)) ∧
            (bh12PathParameter q p z path).rate ≤ epsilon := by sorry
