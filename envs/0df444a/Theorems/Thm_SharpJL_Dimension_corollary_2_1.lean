-- Prove2me | Theorems.Thm_SharpJL_Dimension_corollary_2_1
-- name    : SharpJL.Dimension.corollary_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:08:57.932348+00:00
-- url     : https://prove2.me/theorems/853bf332-2d0b-4e6f-95b0-2c8d91535192
-- title:
--   Corollary 2.1 — linear dimension halving for finite configurations
-- statement:
--   There is a universal constant $C_0>0$ such that, for every pair of integers $n\ge2$ and $r\ge1$, and every finite set $X\subseteq\mathbb R^{2r}$ with $2\le|X|\le n$, there is a real linear map $L:\mathbb R^{2r}\to\mathbb R^r$ satisfying, simultaneously for all $x,y\in X$,
--
--   $$
--   (1-\delta_r)\|x-y\|_2^2\le\|Lx-Ly\|_2^2
--   \le(1+\delta_r)\|x-y\|_2^2,
--   \qquad
--   \delta_r=C_0\sqrt{\frac{\log(2+n/r)}{r}}.
--   $$
--
--   The logarithm is natural, and both norms are Euclidean. The error is defined by this formula, rather than supplied independently. Values $\delta_r\ge1$ are included, so this assertion does not promise injectivity in that regime. This is the squared-distance estimate for halving the ambient dimension of a finite configuration.
--
--   Differences from the source:
--   - encoding: finite subsets of ℝ^(2r) → Finset (EuclideanSpace ℝ (Fin (2 * r))); reason: finite sets of distinct points and the Euclidean norm are unchanged; every finite source set has this representation
-- source:
--   Vishesh Jain, STOC 2027 submission #707 (October 2026), The Sharp Dimension Bound in the Johnson--Lindenstrauss Lemma, Corollary 2.1, p.7 (PDF p.7); §1.4 conventions p.6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/707.pdf#page=7

import Mathlib

namespace SharpJL.Dimension

/-- Jain, STOC 2027 submission #707 (October 2026), Corollary 2.1, p.7.
The explicit error can be at least one; injectivity is not asserted. -/
theorem corollary_2_1 :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (n r : ℕ), 2 ≤ n → 1 ≤ r →
      ∀ (X : Finset (EuclideanSpace ℝ (Fin (2 * r)))),
        2 ≤ X.card → X.card ≤ n →
        ∃ L : EuclideanSpace ℝ (Fin (2 * r)) →ₗ[ℝ] EuclideanSpace ℝ (Fin r),
          let δ := C₀ * Real.sqrt (Real.log (2 + (n : ℝ) / (r : ℝ)) / (r : ℝ))
          ∀ x ∈ X, ∀ y ∈ X,
            (1 - δ) * ‖x - y‖ ^ 2 ≤ ‖L x - L y‖ ^ 2 ∧
              ‖L x - L y‖ ^ 2 ≤ (1 + δ) * ‖x - y‖ ^ 2 := by sorry

end SharpJL.Dimension
