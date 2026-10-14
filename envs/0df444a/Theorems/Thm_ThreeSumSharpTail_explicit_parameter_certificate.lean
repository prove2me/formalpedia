-- Prove2me | Theorems.Thm_ThreeSumSharpTail_explicit_parameter_certificate
-- name    : ThreeSumSharpTail.explicit_parameter_certificate
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-13T14:54:53.237585+00:00
-- url     : https://prove2.me/theorems/c9f11bd4-4101-4aaa-8c30-d0efc095df48
-- title:
--   Exact parameter inequalities for exponent 1.999017
-- statement:
--   For the exact rational parameters $c=21$, $\theta=0.11202$, $a=0.05665$, $s=0.06945$, establish $a(A+\gamma_*)<1$, $s<\gamma_*$, $s<1/2-q$, $\log_2 7+3a/2<3-as/2$, and $2+a(1+s/2)<3-as/2$. Also establish the exact equalities $$2-as/4=1.999016414375,\qquad 1.999017-(2-as/4)=0.000000585625.$$ All decimal constants denote exact rationals (coerced to reals in the analytic inequalities). The source's rational interval checks are reproducible evidence; proving this Lean statement remains a formalization task.
-- source:
--   Yuxuan Xu, Deterministic Integer 3SUM in O(n^1.999017) Time via a Sharper Binomial-Tail Analysis (13 October 2026), Hexagon submission https://hexagonmath.org/submit/d57cba23-2d89-4bcb-8180-7c1bde7d14e3; Section 6.2; parameter certificate used in Theorem 1.1

import Definitions.Def_ThreeSumSharpTail_Analysis
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators

theorem ThreeSumSharpTail.explicit_parameter_certificate :
    (0.05665 : ℝ) * (ThreeSumSharpTail.encodingExponent 21 + ThreeSumSharpTail.sharpSaving 21 0.11202) < 1 ∧
    (0.06945 : ℝ) < ThreeSumSharpTail.sharpSaving 21 0.11202 ∧
    (0.06945 : ℝ) < 1 / 2 - ThreeSumSharpTail.queryExponent 0.11202 ∧
    Real.log 7 / Real.log 2 + 3 * (0.05665 : ℝ) / 2 < 3 - 0.05665 * 0.06945 / 2 ∧
    2 + (0.05665 : ℝ) * (1 + 0.06945 / 2) < 3 - 0.05665 * 0.06945 / 2 ∧
    (2 - (0.05665 : ℚ) * 0.06945 / 4) = 1.999016414375 ∧
    (1.999017 : ℚ) - (2 - 0.05665 * 0.06945 / 4) = 0.000000585625 := by sorry
