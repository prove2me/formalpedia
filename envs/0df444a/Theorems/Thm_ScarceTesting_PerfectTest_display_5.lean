-- Prove2me | Theorems.Thm_ScarceTesting_PerfectTest_display_5
-- name    : ScarceTesting.PerfectTest.display_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:36.991983+00:00
-- url     : https://prove2.me/theorems/a3d48def-458e-4731-ba5f-abd018240031
-- title:
--   Display (5), p. 10 — for a (φ,σ)-test with σ ≥ φ, the critical values satisfy t_L ≤ c ≤ t_H
-- statement:
--   Throughout, $0<c<1$ is the cost-to-benefit ratio of acting (seeking treatment), and a $(\varphi,\sigma)$-test has false positive rate $\varphi$ and true positive rate $\sigma$ with $0\le\varphi\le\sigma\le1$, $\sigma>0$ and $\varphi<1$.
--   The critical values
--   $$t_L=\frac{c\varphi}{c\varphi+(1-c)\sigma},\qquad t_H=\frac{c(1-\varphi)}{c(1-\varphi)+(1-c)(1-\sigma)}$$
--   satisfy
--   $$t_L\le c\le t_H.$$
--
--   This places the cost ratio $c$ between the two thresholds that separate low-, medium- and high-likelihood agents.
--
--   **Formalization Note** The conditions $\sigma>0$ and $\varphi<1$ keep the denominators of $t_L$ and $t_H$ positive (Lean evaluates $0/0$ as $0$); they exclude only the degenerate $(0,0)$- and $(1,1)$-tests.
-- source:
--   Drakopoulos & Randhawa, Why Perfect Tests May Not Be Worth Waiting For: Information as a Commodity, SSRN 3565245 (version of January 13, 2021), display (5) and the sentence following it, p. 10

import Mathlib
import Definitions.Def_ScarceTesting_PerfectTest_Setting

namespace ScarceTesting.PerfectTest

/-- Display (5), p. 10: for a `(φ,σ)`-test with `σ ≥ φ`, `t_L ≤ c ≤ t_H`. -/
theorem display_5 (c φ σ : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1) (hφ0 : 0 ≤ φ) (hφσ : φ ≤ σ) (hσ1 : σ ≤ 1)
    (hσ0 : 0 < σ) (hφ1 : φ < 1) :
    tL c φ σ ≤ c ∧ c ≤ tH c φ σ := by sorry

end ScarceTesting.PerfectTest
