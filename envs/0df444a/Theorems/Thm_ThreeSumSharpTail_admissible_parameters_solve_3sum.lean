-- Prove2me | Theorems.Thm_ThreeSumSharpTail_admissible_parameters_solve_3sum
-- name    : ThreeSumSharpTail.admissible_parameters_solve_3sum
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-13T14:54:18.965287+00:00
-- url     : https://prove2.me/theorems/40c65758-b61e-402e-8afd-d2bc6e1784f1
-- title:
--   From admissible sharp-tail parameters to the shared 3SUM specification
-- statement:
--   Let $c>10$ be an integer, $0<\theta<0.9$, and let $a,s,r$ be rational with $0<a<1$ and $0<s<1$. Suppose
--   $$a(A(c)+\gamma_*(c,\theta))<1,\qquad s<\gamma_*(c,\theta),\qquad s<\tfrac12-q(\theta),$$
--   $$\log_2 7+\tfrac32a<3-as/2,\qquad 2+a(1+s/2)<3-as/2,\qquad r>2-as/4.$$
--   Then deterministic integer 3SUM satisfies the campaign's exact shared predicate `EndStatement.ThreeSum.SolvedInTime r`. This is the combined consequence of Propositions 4.1 and 5.1, not a verbatim separate proposition in the manuscript. Its proof must construct the word-RAM program and establish correctness and all costs using the inherited algorithms and reductions. No inner-algorithm oracle or correctness assumption is supplied as a hypothesis. The uniform word-width requirement in the shared specification is part of the formalization obligation.
-- source:
--   Yuxuan Xu, Deterministic Integer 3SUM in O(n^1.999017) Time via a Sharper Binomial-Tail Analysis (13 October 2026), Hexagon submission https://hexagonmath.org/submit/d57cba23-2d89-4bcb-8180-7c1bde7d14e3; Propositions 4.1 and 5.1; combined consequence

import Definitions.Def_ThreeSumSharpTail_Analysis
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators

theorem ThreeSumSharpTail.admissible_parameters_solve_3sum
    (c : ℕ) (θ : ℝ) (a s r : ℚ) (hc : 10 < c)
    (hθ0 : 0 < θ) (hθ9 : θ < 9 / 10)
    (ha0 : 0 < a) (ha1 : a < 1) (hs0 : 0 < s) (hs1 : s < 1)
    (henc : (a : ℝ) * (ThreeSumSharpTail.encodingExponent c + ThreeSumSharpTail.sharpSaving c θ) < 1)
    (hprep : (s : ℝ) < ThreeSumSharpTail.sharpSaving c θ)
    (hquery : (s : ℝ) < 1 / 2 - ThreeSumSharpTail.queryExponent θ)
    (hprime : Real.log 7 / Real.log 2 + 3 * (a : ℝ) / 2 < 3 - (a : ℝ) * s / 2)
    (hbuild : 2 + (a : ℝ) * (1 + (s : ℝ) / 2) < 3 - (a : ℝ) * s / 2)
    (hr : 2 - a * s / 4 < r) :
    EndStatement.ThreeSum.SolvedInTime r := by sorry
