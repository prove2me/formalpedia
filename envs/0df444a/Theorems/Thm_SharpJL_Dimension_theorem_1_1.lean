-- Prove2me | Theorems.Thm_SharpJL_Dimension_theorem_1_1
-- name    : SharpJL.Dimension.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:09:10.3872+00:00
-- url     : https://prove2.me/theorems/b3bd223a-8164-4eca-839f-6a323c000ec0
-- title:
--   Theorem 1.1 — sharp linear Johnson–Lindenstrauss dimension bound
-- statement:
--   There is a universal constant $C>0$ such that, for all integers $n,d\ge2$, every real parameter $0<\varepsilon<1/2$, and every set $X\subseteq\mathbb R^d$ of exactly $n$ points, there are a nonnegative integer $r$, a real linear map $L:\mathbb R^d\to\mathbb R^r$, and one scale $\lambda>0$ with
--
--   $$
--   r\le C\min\left\{d,n-1,\frac{\log(2+\varepsilon^2n)}{\varepsilon^2}\right\}
--   $$
--
--   and, simultaneously for all $x,y\in X$,
--
--   $$
--   \lambda\|x-y\|_2\le\|Lx-Ly\|_2
--   \le(1+\varepsilon)\lambda\|x-y\|_2.
--   $$
--
--   All norms are Euclidean and the logarithm is natural. The map is linear on the whole ambient space, while the distortion guarantee concerns its restriction to $X$. The universal constant precedes all input data; the map, dimension and scale may depend on the data. This is the paper's main dimension-reduction theorem, including all three entries of the minimum and the entire stated parameter range.
--
--   Differences from the source:
--   - encoding: n-point subsets of ℝ^d → Finset (EuclideanSpace ℝ (Fin d)) with cardinality n; reason: finite sets of distinct points and the Euclidean norm are unchanged; every finite source set has this representation
--   - encoding: an integer target dimension bounded by the three-way minimum → a natural target dimension r, cast to ℝ for the minimum bound, with n−1 computed in ℝ; reason: Euclidean coordinate dimensions are nonnegative integers and n ≥ 2 makes real subtraction agree with the source
-- source:
--   Vishesh Jain, STOC 2027 submission #707 (October 2026), The Sharp Dimension Bound in the Johnson--Lindenstrauss Lemma, Theorem 1.1, p.2 (PDF p.2); §1.4 conventions p.6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/707.pdf#page=2

import Mathlib

namespace SharpJL.Dimension

/-- Jain, STOC 2027 submission #707 (October 2026), Theorem 1.1, p.2,
with the distortion convention of p.1 and natural logarithms as in §1.4, p.6.
One universal constant, all three dimension bounds, ambient linearity,
and one positive scale for all pairs of the configuration are retained. -/
theorem theorem_1_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n d : ℕ), 2 ≤ n → 2 ≤ d →
      ∀ (ε : ℝ), 0 < ε → ε < 1 / 2 →
      ∀ (X : Finset (EuclideanSpace ℝ (Fin d))), X.card = n →
        ∃ (r : ℕ) (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin r))
          (lam : ℝ),
          (r : ℝ) ≤ C * min (d : ℝ)
            (min ((n : ℝ) - 1) (Real.log (2 + ε ^ 2 * (n : ℝ)) / ε ^ 2)) ∧
          0 < lam ∧
          ∀ x ∈ X, ∀ y ∈ X,
            lam * ‖x - y‖ ≤ ‖L x - L y‖ ∧
              ‖L x - L y‖ ≤ (1 + ε) * lam * ‖x - y‖ := by sorry

end SharpJL.Dimension
