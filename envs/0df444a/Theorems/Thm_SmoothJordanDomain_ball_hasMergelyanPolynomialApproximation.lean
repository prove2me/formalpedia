-- Prove2me | Theorems.Thm_SmoothJordanDomain_ball_hasMergelyanPolynomialApproximation
-- name    : SmoothJordanDomain.ball_hasMergelyanPolynomialApproximation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:53:51.009558+00:00
-- url     : https://prove2.me/theorems/0a5942c6-59c0-5548-93af-36f3fc2e70d3
-- title:
--   Smooth Jordan Domain: ball has Mergelyan Polynomial Approximation
-- statement:
--   Every complex function differentiable on an open disk and continuous on
--   its closure is a compact-uniform limit of complex polynomials.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/DiskMergelyan.lean#L112-L191
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/DiskMergelyan.lean#L112-L191

import Definitions.Def_Operator_Crouzeix_SmoothJordanExhaustion
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Definitions.Def_Operator_Crouzeix_DiskMergelyan
set_option autoImplicit false
open Complex Filter Metric Set
open scoped Topology

theorem SmoothJordanDomain.ball_hasMergelyanPolynomialApproximation
    (c : ℂ) (R : ℝ) (hR : 0 < R) :
    (SmoothJordanDomain.ball c R hR).HasMergelyanPolynomialApproximation := by sorry
