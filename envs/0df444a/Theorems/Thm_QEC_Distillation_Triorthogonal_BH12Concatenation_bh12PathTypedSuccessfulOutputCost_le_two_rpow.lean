-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathTypedSuccessfulOutputCost_le_two_rpow
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathTypedSuccessfulOutputCost_le_two_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:33:09.600838+00:00
-- url     : https://prove2.me/theorems/94b40cc3-5168-4c86-98da-4bc6ce021c59
-- title:
--   BH12 Concatenation: bh12 Path Typed Successful Output Cost le two rpow
-- statement:
--   The finite typed physical cost bound can be stated exactly with the
--   fixed-block base-two exponent, without introducing a target-error or
--   asymptotic overhead layer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2559-L2568
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2559-L2568

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathTypedSuccessfulOutputCost_le_two_rpow (q : Nat)
    (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (hq : 0 < q) (z : Nat) (path : depthOutputPath q z) :
    bh12PathTypedSuccessfulOutputCost q p hsmall hhalf hstrong z path ≤
      2 * Real.rpow ((2 : ℝ) ^ z) (bh12BlockExponent q) := by sorry
