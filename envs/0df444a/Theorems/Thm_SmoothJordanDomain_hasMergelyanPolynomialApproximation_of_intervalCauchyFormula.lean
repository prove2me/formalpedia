-- Prove2me | Theorems.Thm_SmoothJordanDomain_hasMergelyanPolynomialApproximation_of_intervalCauchyFormula
-- name    : SmoothJordanDomain.hasMergelyanPolynomialApproximation_of_intervalCauchyFormula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:54:40.342275+00:00
-- url     : https://prove2.me/theorems/678f42f5-488c-4ee5-a891-ed8834531007
-- title:
--   Smooth Jordan Domain: has Mergelyan Polynomial Approximation of interval Cauchy Formula
-- statement:
--   A normalized interval Cauchy formula on a compact smooth convex Jordan
--   carrier implies the full polynomial approximation property.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanMergelyan.lean#L248-L282
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanMergelyan.lean#L248-L282

import Definitions.Def_Operator_Crouzeix_ConvexRungeIntegral
import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchyFormula
import Definitions.Def_Operator_Crouzeix_SmoothJordanExhaustion
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Definitions.Def_Operator_Crouzeix_SmoothJordanMergelyan
set_option autoImplicit false
open Complex Filter Metric Set
open scoped Interval Real Topology

theorem SmoothJordanDomain.hasMergelyanPolynomialApproximation_of_intervalCauchyFormula
    (Omega : SmoothJordanDomain)
    (hcompact : IsCompact (closure Omega.carrier))
    (hCauchy : ∀ (f : ℂ → ℂ), DiffContOnCl ℂ f Omega.carrier →
      ∀ z ∈ Omega.carrier,
        f z = ∫ t in (0 : ℝ)..(2 * Real.pi),
          (2 * (Real.pi : ℂ) * I)⁻¹ * deriv Omega.boundaryParam t *
            f (Omega.boundaryParam t) *
              (Omega.boundaryParam t - z)⁻¹) :
    Omega.HasMergelyanPolynomialApproximation := by sorry
