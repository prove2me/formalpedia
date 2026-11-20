-- Prove2me | Theorems.Thm_RademacherGamma_gaussian_sum_ge_le_quarter
-- name    : RademacherGamma_gaussian_sum_ge_le_quarter
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T10:52:09.372946+00:00
-- url     : https://prove2.me/theorems/e5b7f99d-1d3f-478f-ab2c-a0a015774877
-- title:
--   Gaussian difference series lower bound for 0 < delta <= 1/4
-- statement:
--   For all real $y, \delta, t$ with $y \ge \frac{1}{4}$, $0 < \delta \le \frac{1}{4}$, and $t > 0$,
--
--   $$
--   2\delta e^{-y^2 t} \le \sum_{k=0}^{\infty} \left(e^{-(y + k - \delta)^2 t} - e^{-(y + k + \delta)^2 t}\right).
--   $$
--
--   This establishes the $\delta \in (0, 1/4]$ half of the Gaussian series positivity inequality needed for Rademacher's Gamma-ratio bound.
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

theorem RademacherGamma_gaussian_sum_ge_le_quarter {y δ t : ℝ}
    (hy : 1 / 4 ≤ y) (hδ0 : 0 < δ) (hδ_le : δ ≤ 1 / 4) (ht : 0 < t) :
    2 * δ * Real.exp (-y ^ 2 * t) ≤
      ∑' k : ℕ, (Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t)) := by sorry
