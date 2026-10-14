-- Prove2me | Theorems.Thm_ThreeSumSharpTail_rational_theta_certificate
-- name    : ThreeSumSharpTail.rational_theta_certificate
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-13T17:49:26.03352+00:00
-- url     : https://prove2.me/theorems/d73bb009-45ef-4d29-a264-1b5aaa5ffb59
-- title:
--   Rational switch parameter preserving strict certificate margins
-- statement:
--   Fix an integer c>10, real theta in (0,9/10), and rational a,s. If a(A(c)+Gamma(c,theta))<1, s<Gamma(c,theta), and s<1/2-q(theta), then there is a rational eta in (0,9/10) satisfying the same three strict inequalities. This gives a finite rational switch parameter for the program while preserving the encoding, preprocessing and query margins.
-- source:
--   Derived parameter selection lemma for Xu, Deterministic Integer 3SUM in O(n^1.999017) Time via a Sharper Binomial-Tail Analysis, Sections 3-4. Continuity and rational density justify the finite program implementation of the real switch parameter.

import Definitions.Def_ThreeSumSharpTail_Analysis
set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSumSharpTail

theorem ThreeSumSharpTail.rational_theta_certificate (c : ℕ) (θ : ℝ) (a s : ℚ)
    (hc : 10 < c) (hθ0 : 0 < θ) (hθ9 : θ < 9 / 10)
    (henc : (a : ℝ) * (encodingExponent c + sharpSaving c θ) < 1)
    (hprep : (s : ℝ) < sharpSaving c θ)
    (hquery : (s : ℝ) < 1 / 2 - queryExponent θ) :
    ∃ η : ℚ, 0 < (η : ℝ) ∧ (η : ℝ) < 9 / 10 ∧
      (a : ℝ) * (encodingExponent c + sharpSaving c (η : ℝ)) < 1 ∧
      (s : ℝ) < sharpSaving c (η : ℝ) ∧
      (s : ℝ) < 1 / 2 - queryExponent (η : ℝ) := by sorry
