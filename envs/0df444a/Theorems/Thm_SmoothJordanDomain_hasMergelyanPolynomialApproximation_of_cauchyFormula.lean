-- Prove2me | Theorems.Thm_SmoothJordanDomain_hasMergelyanPolynomialApproximation_of_cauchyFormula
-- name    : SmoothJordanDomain.hasMergelyanPolynomialApproximation_of_cauchyFormula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:54:23.013806+00:00
-- url     : https://prove2.me/theorems/3bd4c384-322d-560c-b0bd-57bdcb2a7a3f
-- title:
--   Smooth Jordan Domain: has Mergelyan Polynomial Approximation of cauchy Formula
-- statement:
--   The contour form of the normalized Cauchy formula implies the same
--   polynomial approximation property.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanMergelyan.lean#L286-L304
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanMergelyan.lean#L286-L304

import Definitions.Def_Operator_Crouzeix_ConvexRungeIntegral
import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchyFormula
import Definitions.Def_Operator_Crouzeix_SmoothJordanExhaustion
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Definitions.Def_Operator_Crouzeix_SmoothJordanMergelyan
set_option autoImplicit false
open Complex Filter Metric Set
open scoped Interval Real Topology

theorem SmoothJordanDomain.hasMergelyanPolynomialApproximation_of_cauchyFormula
    (Omega : SmoothJordanDomain)
    (hcompact : IsCompact (closure Omega.carrier))
    (hCauchy : ∀ (f : ℂ → ℂ), DiffContOnCl ℂ f Omega.carrier →
      ∀ z ∈ Omega.carrier,
        f z = (2 * (Real.pi : ℂ) * I)⁻¹ *
          contourIntegral (fun xi => f xi * (xi - z)⁻¹)
            Omega.boundaryParam) :
    Omega.HasMergelyanPolynomialApproximation := by sorry
