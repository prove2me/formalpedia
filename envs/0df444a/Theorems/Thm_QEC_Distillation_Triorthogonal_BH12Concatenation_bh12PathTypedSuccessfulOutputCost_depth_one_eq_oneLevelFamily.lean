-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathTypedSuccessfulOutputCost_depth_one_eq_oneLevelFamily
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathTypedSuccessfulOutputCost_depth_one_eq_oneLevelFamily
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:33:53.56961+00:00
-- url     : https://prove2.me/theorems/f89b788a-9a56-42e5-8425-eb4d16e3506f
-- title:
--   BH12 Concatenation: bh12 Path Typed Successful Output Cost depth one eq one Level Family
-- statement:
--   At depth one, the typed finite-slot adapter is exactly the #458
--   successful-output cost of the actual selected one-level BH12 family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2844-L2869
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2844-L2869

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathTypedSuccessfulOutputCost_depth_one_eq_oneLevelFamily
    (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (path : depthOutputPath q 1) :
    bh12PathTypedSuccessfulOutputCost q p hsmall hhalf hstrong 1 path =
      (bh12OneLevelProtocolFamily q p hhalf).successfulOutputCost (path 0) := by sorry
