-- Prove2me | Theorems.Thm_RademacherGamma_gaussian_sum_ge
-- name    : RademacherGamma_gaussian_sum_ge
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T10:52:07.413823+00:00
-- url     : https://prove2.me/theorems/d394af06-053b-4225-858c-d825a1787a45
-- title:
--   Global Gaussian difference series lower bound for 0 < delta < 1/2
-- statement:
--   For all real $y, \delta, t$ satisfying $y \ge \frac{1}{4}$, $0 < \delta < \frac{1}{2}$, and $t > 0$,
--
--   $$
--   2\delta e^{-y^2 t} \le \sum_{k=0}^{\infty} \left(e^{-(y + k - \delta)^2 t} - e^{-(y + k + \delta)^2 t}\right).
--   $$
--
--   This global inequality ensures nonnegativity of the Laplace-transform integrand in Rademacher's Gamma-ratio monotonicity proof.
-- source:
--   LL_Decomp530a.leaf_rademacher_gamma_ratio (Rademacher Gamma-ratio inequality helper)

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open Real MeasureTheory Filter Set
open scoped Topology

theorem RademacherGamma_gaussian_sum_ge {y δ t : ℝ}
    (hy : 1 / 4 ≤ y) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) (ht : 0 < t) :
    2 * δ * Real.exp (-y ^ 2 * t) ≤
      ∑' k : ℕ, (Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t)) := by sorry
