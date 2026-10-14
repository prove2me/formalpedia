-- Prove2me | Theorems.Thm_ThreeSum1960614_integer_schedule
-- name    : ThreeSum1960614.integer_schedule
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-14T05:08:34.601986+00:00
-- url     : https://prove2.me/theorems/23685129-7595-4605-accf-6de4710e077b
-- title:
--   Least integer quartic switch and uniform rounding bounds
-- statement:
--   For arbitrary positive natural block count $J$, positive even microblock size $s$, and level $0\le j<J$ with $j/J\le13/20$, let $r=(J-j)s$ and $\mu=Js$. There exists a positive least integer $q\le r/2$ satisfying the cleared integer comparison, and every smaller natural number fails it. This same $q$ satisfies $K\le P(q/r)<K+9/r$ for $K=(v+j/J)/(1-j/J)$. It also satisfies $S\le2b-j/J+(1-j/J)\gamma_{232}(q/r)$ and $(1-j/J)H(q/r)<\rho(1+v)+9\rho/\mu$. No divisibility of $J$ is needed for these per-level bounds; positivity and evenness make $r/2$ an integer and every real denominator nonzero.
-- source:
--   User-supplied 3sum_certificate_1p960614_v3/3sum_certificate_v3/PROOF.md (14 October 2026); Section 4.2–4.3; upstream https://github.com/c0ldzy17/three-sum-lean/tree/2b639655e07421b9ac743de9090459bab473a7c0

import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614

theorem ThreeSum1960614.integer_schedule (J s j : ℕ)
    (hJ : 0 < J) (hs : 0 < s) (heven : Even s) (hj : j < J)
    (hlevel : (j : ℝ) / J ≤ tau) :
    ∃ q : ℕ, 0 < q ∧ q ≤ ((J - j) * s) / 2 ∧ clearedSwitch J s j q ∧
      (∀ k < q, ¬ clearedSwitch J s j k) ∧
      threshold ((j : ℝ) / J) ≤ phi ((q : ℝ) / ((J - j) * s)) ∧
      phi ((q : ℝ) / ((J - j) * s)) <
        threshold ((j : ℝ) / J) + 9 / ((J - j) * s) ∧
      saving ≤ 2 * beta - (j : ℝ) / J +
        (1 - (j : ℝ) / J) * gamma 232 ((q : ℝ) / ((J - j) * s)) ∧
      (1 - (j : ℝ) / J) * entropy ((q : ℝ) / ((J - j) * s)) <
        rho * (1 + v) + 9 * rho / (J * s) := by sorry
