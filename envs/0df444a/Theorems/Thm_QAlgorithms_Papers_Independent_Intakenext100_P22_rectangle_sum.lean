-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P22_rectangle_sum
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P22.rectangle_sum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:50:04.570735+00:00
-- url     : https://prove2.me/theorems/e76f4041-1e40-4773-b5b0-d8da22fee448
-- title:
--   Closed formulas for a cosine rectangle sum
-- statement:
--   Let $n\ge2$, $1\le k<n$ be integers. Let $p,q,\lambda_r,\lambda_c\ge0$ be integers with $p+\lambda_r\le n-1$ and $q+\lambda_c\le n-1$. Put $t=\pi k/n$ and
--   $$S=\sum_{i=p+1}^{p+\lambda_r}\sum_{j=q+1}^{q+\lambda_c}\cos(2t(i-j)).$$
--   Then
--   $$S=\frac{\sin(t\lambda_r)\sin(t\lambda_c)}{\sin^2t}\cos[t(2(p-q)+\lambda_r-\lambda_c)]$$
--   and
--   $$S=\frac{\sin^2[t(p-q+\lambda_r)]+\sin^2[t(p-q-\lambda_c)]-\sin^2[t(p-q+\lambda_r-\lambda_c)]-\sin^2[t(p-q)]}{2\sin^2t}.$$
--   Zero side lengths are allowed and give zero. This finite identity evaluates the cosine contractions of the lattice-sector patterns.
-- source:
--   Entanglement entropy of two disjoint intervals in conformal field theory II, arXiv:1011.5482v1, PDF p. 18, §5.4, equations (86)–(88)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P22

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P22

open scoped BigOperators Topology

open Filter MeasureTheory

/-- PDF p. 18, (86)–(88): both rectangle evaluations, including sine
squares in all four terms of (88). Zero side lengths are permitted. -/
theorem rectangle_sum (n k p lr q lc : ℕ) (hn : 2 ≤ n)
    (hk : 1 ≤ k) (hkn : k < n) (hr : p + lr ≤ n - 1) (hc : q + lc ≤ n - 1) :
    let t : ℝ := Real.pi * (k : ℝ) / n
    rectangleSum n k p lr q lc =
      Real.sin (t * lr) * Real.sin (t * lc) / Real.sin t ^ 2 *
        Real.cos (t * (2 * ((p : ℝ) - q) + lr - lc)) ∧
    rectangleSum n k p lr q lc =
      (Real.sin (t * ((p : ℝ) - q + lr)) ^ 2 +
       Real.sin (t * ((p : ℝ) - q - lc)) ^ 2 -
       Real.sin (t * ((p : ℝ) - q + lr - lc)) ^ 2 -
       Real.sin (t * ((p : ℝ) - q)) ^ 2) / (2 * Real.sin t ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P22

end
