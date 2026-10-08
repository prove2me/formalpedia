-- Prove2me | Theorems.Thm_RhinViola_weightedGeometricKernelHasSum
-- name    : RhinViola.weightedGeometricKernelHasSum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T21:37:13.745204+00:00
-- url     : https://prove2.me/theorems/da21900b-cc7b-4637-89e8-e8fbef99cebb
-- title:
--   Pointwise weighted geometric expansion of the monomial kernel
-- statement:
--   For nonnegative x,y with xy<1, the weighted geometric series sum_k x^(h+k)y^(m+k) converges to x^h y^m/(1-xy). This is the pointwise series expansion of the Rhin-Viola monomial kernel away from the singular corner (1,1).
-- source:
--   Geometric-series expansion used in G. Rhin and C. Viola, On the irrationality measure of zeta(2), Annales de l'Institut Fourier 43 (1993), Section 3.

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

theorem RhinViola.weightedGeometricKernelHasSum
    (h m : ℕ) (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x * y < 1) :
    HasSum (fun k : ℕ => x ^ (h + k) * y ^ (m + k))
      (x ^ h * y ^ m / (1 - x * y)) := by sorry
