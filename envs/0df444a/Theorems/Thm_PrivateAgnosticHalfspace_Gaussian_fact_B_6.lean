-- Prove2me | Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_fact_B_6
-- name    : PrivateAgnosticHalfspace.Gaussian.fact_B_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T11:24:48.117593+00:00
-- url     : https://prove2.me/theorems/71e62888-279e-4838-81d6-ef7da4225272
-- title:
--   Fact B.6 — random thresholding
-- statement:
--   Let $\tau$ be uniform on $[-1,1]$. For every real score $z$ and every label $y\in\{-1,1\}$,
--   $$
--   \Pr_{\tau}[\operatorname{sign}(z-\tau)\ne y]\le\frac12|z-y|.
--   $$
--   This includes scores outside $[-1,1]$. The probability is the normalized restricted Lebesgue measure, and the sign at zero is $+1$.
--
--   The inequality connects absolute regression loss to classification error under random thresholds.
--
--   Differences from the source:
--   - encoding: labels in {−1,1} and an unspecified binary sign at a tie → Bool labels decoded as ±1 and sign(0)=+1; reason: the threshold law has no atoms, so the tie convention changes no probability instance
-- source:
--   Giorgio Racca, Amartya Sanyal, Vikrant Singhal, STOC 2027 submission #1006 (October 2026), p. 22, Fact B.6; canonical PDF sha256 f0122a33e29daa624b530bdd0b071998d8e44197b30449b0cb3213289645cec7

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Regression

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivateAgnosticHalfspace.Gaussian

theorem fact_B_6 (z : ℝ) (y : Bool) :
    (((2 : ℝ≥0∞)⁻¹ • volume.restrict (Set.Icc (-1 : ℝ) 1)) : Measure ℝ).real
      {τ | sign (z - τ) ≠ y} ≤ |z - label y| / 2 := by sorry

end PrivateAgnosticHalfspace.Gaussian
