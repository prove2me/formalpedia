-- Prove2me | Theorems.Thm_RhinViola_monomialKernelLIntegralEqGeometricSeries
-- name    : RhinViola.monomialKernelLIntegralEqGeometricSeries
-- status  : Open
-- author  : @WillR
-- created : 2026-10-06T11:45:08.330526+00:00
-- url     : https://prove2.me/theorems/2033045f-354b-46f1-aad9-045d4bf30d7b
-- title:
--   Unit-square monomial kernel lintegral equals its geometric-series lintegral
-- statement:
--   On the unit square, the ENNReal geometric-series integrand agrees almost everywhere with the embedded real kernel x^h y^m/(1-xy). The only excluded outer point is x=1, which is Lebesgue-null; for every remaining x in (0,1] the pointwise identity holds for all y in (0,1]. Hence the nested lintegrals coincide.
-- source:
--   Geometric-series/Tonelli identification in G. Rhin and C. Viola, On the irrationality measure of zeta(2), Annales de l'Institut Fourier 43 (1993), Section 3.

import Theorems.Thm_RhinViola_weightedGeometricKernelENNRealTsumIoc
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

theorem RhinViola.monomialKernelLIntegralEqGeometricSeries
    (h m : ℕ) :
    (∫⁻ x : ℝ in Set.Ioc (0 : ℝ) 1,
      ∫⁻ y : ℝ in Set.Ioc (0 : ℝ) 1,
        ∑' k : ℕ,
          ENNReal.ofReal (x ^ (h + k)) *
            ENNReal.ofReal (y ^ (m + k))) =
      (∫⁻ x : ℝ in Set.Ioc (0 : ℝ) 1,
        ∫⁻ y : ℝ in Set.Ioc (0 : ℝ) 1,
          ENNReal.ofReal
            (x ^ h * y ^ m / (1 - x * y))) := by sorry
