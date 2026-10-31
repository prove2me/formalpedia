-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P23_winding_coefficient_identity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P23.winding_coefficient_identity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:33:06.404998+00:00
-- url     : https://prove2.me/theorems/ee56a9ac-184b-4ded-93fc-bc838f46819d
-- title:
--   Leading winding coefficient logarithm
-- statement:
--   Let $n\ge2$, $1\le\ell<n$, and let $m$ be any constant-sign block of length $\ell$ in $\mathbb Z^{n-1}$. Let $C_{k/n}$ be the cosine matrix above, let $\gamma_E$ be Euler's constant, and put $f_y=2\gamma_E+\psi(y)+\psi(1-y)$, where $\psi=\Gamma'/\Gamma$ is the digamma function. Then
--   $$\frac2n\sum_{k=1}^{n-1}\sin^2(\pi k/n)f_{k/n}\,m^{\mathsf T}C_{k/n}m=-\log\!\left([2n\sin(\pi\ell/n)]^2\right).$$
--   This evaluates the block coefficient without dependence on block start or sign. The logarithm contains the square of the entire bracket.
-- source:
--   Entanglement entropy of two disjoint intervals in conformal field theory, arXiv:0905.2069v2, PDF p. 15, Eq. (71)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P23

noncomputable section

open scoped BigOperators Topology

open Filter Set MeasureTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P23

/-- Source p.15, Eq.(71). The logarithm is of the square of the ENTIRE
quantity 2n sin(pi ell/n), independent of block start and sign. -/
theorem winding_coefficient_identity (n ell : ℕ) (hn : 2 ≤ n)
    (hell : 1 ≤ ell ∧ ell < n) (a : Fin (n - ell)) (s : Bool) :
    2 / (n : ℝ) * (∑ k : Fin (n - 1),
      Real.sin (Real.pi * ((k.val + 1 : ℕ) : ℝ) / (n : ℝ)) ^ 2 *
      windingConstant (((k.val + 1 : ℕ) : ℝ) / (n : ℝ)) *
      QAlgorithms.Papers.Independent.Information100.P37.quadratic (cosineMatrix n (k.val + 1) (n - 1))
        (fun j => (windingBlock n ell a.val s j : ℝ))) =
    -Real.log ((2 * (n : ℝ) * Real.sin (Real.pi * (ell : ℝ) / (n : ℝ))) ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P23

end
