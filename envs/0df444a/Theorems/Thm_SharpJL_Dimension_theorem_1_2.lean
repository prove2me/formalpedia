-- Prove2me | Theorems.Thm_SharpJL_Dimension_theorem_1_2
-- name    : SharpJL.Dimension.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:08:59.297108+00:00
-- url     : https://prove2.me/theorems/6b9282cb-cd77-4820-a354-ac216db1396b
-- title:
--   Theorem 1.2 — positive semidefinite rank halving
-- statement:
--   There is a universal constant $C>0$ such that, for every pair of integers $r,m\ge1$ and every indexed family of Euclidean unit vectors $u_1,\ldots,u_m\in\mathbb R^{2r}$, there is a real positive semidefinite matrix $M$ of order $2r$ with
--
--   $$
--   \operatorname{rank} M\le r,\qquad
--   \max_{1\le\ell\le m}|u_\ell^{\mathsf T}Mu_\ell-1|
--   \le C\sqrt{\frac{\log(2+m/r^2)}{r}}.
--   $$
--
--   The logarithm is natural. The constant is independent of the dimensions and the vectors. The matrix may be singular; vectors may repeat, and no restriction on the size of the error is assumed. This is the rank-halving statement used for finite-configuration dimension reduction.
--
--   Differences from the source:
--   - encoding: m indexed unit vectors in ℝ^(2r) → Fin m indexed families in EuclideanSpace ℝ (Fin (2 * r)); reason: zero-based coordinates and indices change no instances and allow repeated vectors
--   - encoding: a maximum over the m prescribed quadratic-form errors → the displayed error bound holds for every index in Fin m; reason: m ≥ 1 makes the pointwise bound equivalent to the finite maximum bound
-- source:
--   Vishesh Jain, STOC 2027 submission #707 (October 2026), The Sharp Dimension Bound in the Johnson--Lindenstrauss Lemma, Theorem 1.2, p.3 (PDF p.3); §1.4 conventions p.6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/707.pdf#page=3

import Mathlib

namespace SharpJL.Dimension

/-- Jain, STOC 2027 submission #707 (October 2026), Theorem 1.2, p.3.
The constant precedes all input dimensions and unit-vector families.
Positive semidefiniteness includes symmetry; singular matrices are allowed. -/
theorem theorem_1_2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (r m : ℕ), 1 ≤ r → 1 ≤ m →
      ∀ (u : Fin m → EuclideanSpace ℝ (Fin (2 * r))),
        (∀ ℓ, ‖u ℓ‖ = 1) →
        ∃ M : Matrix (Fin (2 * r)) (Fin (2 * r)) ℝ,
          M.PosSemidef ∧ M.rank ≤ r ∧
          ∀ ℓ : Fin m,
            |(∑ i : Fin (2 * r), ∑ j : Fin (2 * r), u ℓ i * M i j * u ℓ j) - 1| ≤
              C * Real.sqrt (Real.log (2 + (m : ℝ) / (r : ℝ) ^ 2) / (r : ℝ)) := by sorry

end SharpJL.Dimension
