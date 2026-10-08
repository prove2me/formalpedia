-- Prove2me | Theorems.Thm_RhinViola_weightedGeometricKernelENNRealTsum
-- name    : RhinViola.weightedGeometricKernelENNRealTsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T22:48:57.102371+00:00
-- url     : https://prove2.me/theorems/8981df56-89f6-4d20-bf3b-9449c4e7ae82
-- title:
--   ENNReal tsum form of the weighted geometric monomial kernel
-- statement:
--   For nonnegative x and y with xy<1, the ENNReal tsum used by Tonelli is exactly the ENNReal embedding of the real monomial kernel x^h y^m/(1-xy). The proof lifts the existing real weighted-geometric HasSum using the nonnegative-series ofReal/tsum bridge.
-- source:
--   Geometric-series/Tonelli bridge in G. Rhin and C. Viola, On the irrationality measure of zeta(2), Annales de l'Institut Fourier 43 (1993), Section 3.

import Theorems.Thm_RhinViola_weightedGeometricKernelHasSum
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic

theorem RhinViola.weightedGeometricKernelENNRealTsum
    (h m : ℕ) (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x * y < 1) :
    (∑' k : ℕ,
      ENNReal.ofReal (x ^ (h + k)) *
        ENNReal.ofReal (y ^ (m + k))) =
      ENNReal.ofReal (x ^ h * y ^ m / (1 - x * y)) := by sorry
