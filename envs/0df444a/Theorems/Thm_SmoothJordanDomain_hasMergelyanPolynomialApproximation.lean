-- Prove2me | Theorems.Thm_SmoothJordanDomain_hasMergelyanPolynomialApproximation
-- name    : SmoothJordanDomain.hasMergelyanPolynomialApproximation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:52:04.975199+00:00
-- url     : https://prove2.me/theorems/43b8f56c-3928-5439-88e6-332b755dde2e
-- title:
--   Smooth Jordan Domain: has Mergelyan Polynomial Approximation
-- statement:
--   Every smooth strictly convex Jordan domain has the polynomial
--   approximation property on its closed carrier.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanMergelyan.lean#L308-L335
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanMergelyan.lean#L308-L335

import Definitions.Def_Operator_Crouzeix_ConvexRungeIntegral
import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchyFormula
import Definitions.Def_Operator_Crouzeix_SmoothJordanExhaustion
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Definitions.Def_Operator_Crouzeix_SmoothJordanMergelyan
set_option autoImplicit false
open Complex Filter Metric Set
open scoped Interval Real Topology

theorem SmoothJordanDomain.hasMergelyanPolynomialApproximation
    (Omega : SmoothJordanDomain) :
    Omega.HasMergelyanPolynomialApproximation := by sorry
