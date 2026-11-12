-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathParameter_exists_depth_rate_le
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathParameter_exists_depth_rate_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:31:57.003529+00:00
-- url     : https://prove2.me/theorems/e0c4c9b5-7dfd-4c00-8380-d7fa4df8b3cd
-- title:
--   BH12 Concatenation: bh12 Path Parameter exists depth rate le
-- statement:
--   A strict initial BH12 coefficient condition gives one finite depth that
--   uniformly bounds the recursively derived rate along every selected-port path.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1906-L1919
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1906-L1919

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathParameter_exists_depth_rate_le (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hquadraticSmall : quadraticCoefficient q * p.rate ≤ 1)
    (hstrict : quadraticCoefficient q * p.rate < 1)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ z : Nat, ∀ path : depthOutputPath q z,
      (bh12PathParameter q p z path).rate ≤ epsilon := by sorry
