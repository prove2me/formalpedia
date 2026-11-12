-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathNextResources_eq_noisyResources
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathNextResources_eq_noisyResources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:36:25.060593+00:00
-- url     : https://prove2.me/theorems/2765a6b4-b593-4916-ad24-be7ae2a98ff8
-- title:
--   BH12 Concatenation: bh12 Path Next Resources eq noisy Resources
-- statement:
--   Under the initial three inequalities, the literal fresh-parent resource
--   family at every path step is the standard noisy-resource family at the total
--   next parameter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1596-L1610
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1596-L1610

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathNextResources_eq_noisyResources (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hquadraticSmall : quadraticCoefficient q * p.rate ≤ 1)
    (z : Nat) (path : depthOutputPath q z) (port : OddRow q) :
    bh12PathNextResources q p z path port =
      noisyResources q
        (bh12TotalNextParameter q (bh12PathParameter q p z path) port) := by sorry
