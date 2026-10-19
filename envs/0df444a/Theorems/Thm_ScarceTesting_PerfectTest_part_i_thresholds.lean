-- Prove2me | Theorems.Thm_ScarceTesting_PerfectTest_part_i_thresholds
-- name    : ScarceTesting.PerfectTest.part_i_thresholds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:37.249824+00:00
-- url     : https://prove2.me/theorems/28ddf8df-20de-499b-b293-81a00d38d7a9
-- title:
--   Proof of Proposition 2(i), pp. 22–23 — for the (φ,1)-test, t_H = 1, t_L(φ) = cφ/(cφ + (1−c)) and dt_L/dφ(0) = c/(1−c)
-- statement:
--   Let $0<c<1$. For tests with true positive rate $\sigma=1$:
--
--   1. $t_H=1$ whenever $\varphi<1$;
--   2. $t_L(\varphi)=\dfrac{c\varphi}{c\varphi+(1-c)}$;
--   3. $$\frac{dt_L}{d\varphi}(0)=\frac{c}{1-c}.$$
--
--   These are the first computations in part (i) of the proof of Proposition 2, which perturbs the perfect test by a small false positive rate.
-- source:
--   Drakopoulos & Randhawa, Why Perfect Tests May Not Be Worth Waiting For: Information as a Commodity, SSRN 3565245 (version of January 13, 2021), proof of Proposition 2 (Appendix A.1.2), part (i), pp. 22–23, "since σ = 1, we have t_H = 1" and "We first note that t_L(φ) = …"

import Mathlib
import Definitions.Def_ScarceTesting_PerfectTest_Setting

namespace ScarceTesting.PerfectTest

/-- Proof of Proposition 2(i), pp. 22–23: for the `(φ,1)`-test, `t_H = 1`,
`t_L(φ) = cφ/(cφ + (1−c))`, and `dt_L/dφ(0) = c/(1−c)`. -/
theorem part_i_thresholds (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    (∀ φ : ℝ, φ < 1 → tH c φ 1 = 1) ∧
    (∀ φ : ℝ, tL c φ 1 = c * φ / (c * φ + (1 - c))) ∧
    HasDerivAt (fun φ => tL c φ 1) (c / (1 - c)) 0 := by sorry

end ScarceTesting.PerfectTest
