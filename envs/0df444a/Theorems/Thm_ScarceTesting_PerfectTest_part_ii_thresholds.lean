-- Prove2me | Theorems.Thm_ScarceTesting_PerfectTest_part_ii_thresholds
-- name    : ScarceTesting.PerfectTest.part_ii_thresholds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:32.676661+00:00
-- url     : https://prove2.me/theorems/dcebabae-1e01-4877-8ae8-062a86a7ffa8
-- title:
--   Proof of Proposition 2(ii), pp. 23–24 — for the (0,σ)-test, t_L = 0, t_H(σ) = c/(1−(1−c)σ) and dt_H/dσ(1) = (1−c)/c
-- statement:
--   Let $0<c<1$. For tests with false positive rate $\varphi=0$:
--
--   1. $t_L=0$;
--   2. $t_H(\sigma)=\dfrac{c}{1-(1-c)\sigma}$;
--   3. $$\frac{dt_H}{d\sigma}(1)=\frac{1-c}{c}.$$
--
--   These are the first computations in part (ii) of the proof of Proposition 2, which perturbs the perfect test by a true positive rate slightly below $1$.
--
--   **Formalization Note** The identities hold for every real $\sigma$ (Lean's $x/0=0$ makes $t_L=0$ even at $\sigma=0$, and $c+(1-c)(1-\sigma)=1-(1-c)\sigma$ identically).
-- source:
--   Drakopoulos & Randhawa, Why Perfect Tests May Not Be Worth Waiting For: Information as a Commodity, SSRN 3565245 (version of January 13, 2021), proof of Proposition 2 (Appendix A.1.2), part (ii), pp. 23–24, "because φ = 0, we have t_L = 0" and "We first note that t_H(σ) = …"

import Mathlib
import Definitions.Def_ScarceTesting_PerfectTest_Setting

namespace ScarceTesting.PerfectTest

/-- Proof of Proposition 2(ii), pp. 23–24: for the `(0,σ)`-test, `t_L = 0`,
`t_H(σ) = c/(1 − (1−c)σ)`, and `dt_H/dσ(1) = (1−c)/c`. -/
theorem part_ii_thresholds (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    (∀ σ : ℝ, tL c 0 σ = 0) ∧
    (∀ σ : ℝ, tH c 0 σ = c / (1 - (1 - c) * σ)) ∧
    HasDerivAt (fun σ => tH c 0 σ) ((1 - c) / c) 1 := by sorry

end ScarceTesting.PerfectTest
