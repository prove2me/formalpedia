-- Prove2me | Theorems.Thm_ThreeSumSharpTail_sharp_saving_strict
-- name    : ThreeSumSharpTail.sharp_saving_strict
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-13T14:53:54.078103+00:00
-- url     : https://prove2.me/theorems/3adf4d69-99ea-45b7-b6c0-7c5db9bd4123
-- title:
--   Strict improvement of the preprocessing saving
-- statement:
--   For every real $c>10$ and $0<\theta<0.9$, $$\gamma_*(c,\theta)>\gamma(c,\theta)>0.$$ This compares preprocessing savings at the same parameters. It does not by itself establish a smaller 3SUM running-time exponent.
-- source:
--   Yuxuan Xu, Deterministic Integer 3SUM in O(n^1.999017) Time via a Sharper Binomial-Tail Analysis (13 October 2026), Hexagon submission https://hexagonmath.org/submit/d57cba23-2d89-4bcb-8180-7c1bde7d14e3; Proposition 3.3

import Definitions.Def_ThreeSumSharpTail_Analysis
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators

theorem ThreeSumSharpTail.sharp_saving_strict (c θ : ℝ) (hc : 10 < c)
    (hθ0 : 0 < θ) (hθ9 : θ < 9 / 10) :
    0 < ThreeSumSharpTail.oldSaving c θ ∧
    ThreeSumSharpTail.oldSaving c θ < ThreeSumSharpTail.sharpSaving c θ := by sorry
