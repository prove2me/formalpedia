-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_interior_integer_grid_bound
-- name    : QuantumBipartiteTesting.Bipartiteness.interior_integer_grid_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T13:43:48.274214+00:00
-- url     : https://prove2.me/theorems/4c870677-f2cd-4476-b81c-f377785662bd
-- title:
--   Interior bound for a polynomial on an integer grid
-- statement:
--   Let $m$ be a positive integer and let $p$ be a real univariate polynomial of degree less than $2m+2$. Suppose
--
--   $$
--   |p(x)|\le 1\qquad\text{for every integer }-16m\le x\le16m+1.
--   $$
--
--   Then
--
--   $$
--   |p(z)|\le\frac43\qquad\text{for every real }0\le z\le1.
--   $$
--
--   This quantitative interior estimate bounds the growth between adjacent grid points when the degree is small compared with their distance from the ends of the integer interval. It supplies the interior case of the translated arithmetic-grid degree argument.
-- source:
--   Auxiliary interior estimate for Lemma 2.12 of Kayal–Sen–Szabó, held October 2026 manuscript, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf; compare Ambainis–Childs–Liu 2011, https://arxiv.org/pdf/1012.3174, §C.3 Theorem 18 and Lemma 4. Symmetric finite-difference weights adapted from Saint Wesonga, https://github.com/formalcs/circuit-complexity/tree/release/0.2.0/Majority/ApproximateDegree, LowerBoundGrid.lean and MajorityWitness.lean (Apache 2.0); the fractional divided-difference estimate gives the explicit mesh sixteen and bound four-thirds.

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction

theorem QuantumBipartiteTesting.Bipartiteness.interior_integer_grid_bound
    (m : ℕ) (hm : 0 < m) (p : Polynomial ℝ) (hp : p.natDegree < 2*m+2)
    (hb : ∀ x : ℤ, -(16*(m:ℤ)) ≤ x → x ≤ 16*(m:ℤ)+1 → |p.eval (x:ℝ)| ≤ 1) :
    ∀ z : ℝ, 0 ≤ z → z ≤ 1 → |p.eval z| ≤ 4/3 := by sorry
