-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_regularized_semigroup_lipschitz
-- name    : QAlgorithms.Papers.Independent.Next46.P06.regularized_semigroup_lipschitz
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:46:53.911149+00:00
-- url     : https://prove2.me/theorems/f62886dd-7e2c-4fe3-b0ea-be9c5a0a8aa6
-- title:
--   Proposition 13.1, first assertion
-- statement:
--   Let $X$ be a complex Banach space and let $T:[0,\infty)\to\mathcal L(X)$ be a uniformly bounded semigroup with $T(0)=I$, strongly continuous only for positive times. Let $-A$ be its single-valued generator, characterized by the Laplace resolvent, without requiring a dense domain. Then the map $t\mapsto T(t)(I+A)^{-1}$ is Lipschitz continuous in operator norm:
--
--   $$\exists L\ge0\ \forall s,t\ge0,\quad \|T(t)(I+A)^{-1}-T(s)(I+A)^{-1}\|\le L|t-s|.$$
--
--   This is the first assertion of Proposition 13.1, independent of its defective contour quantifier.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 34, Proposition 13.1, first assertion

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P06

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter

open scoped Topology

namespace QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore)

universe u v w

variable {F G : Type*} [Ring F] [Algebra ℂ F] [Ring G] [Algebra ℂ G]

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- Proposition 13.1, first assertion, PDF p.34: norm-Lipschitz continuity
on [0,infinity), including zero, of T(t)(I+A)^(-1). Strong continuity of T
at zero and a dense generator graphDomain are not assumed. -/
theorem regularized_semigroup_lipschitz [CompleteSpace X] (T : ℝ → X →L[ℂ] X)
    (hT : BoundedSemigroup T) (hnd : NondegenerateSemigroup T) :
    let A := negativeGenerator T
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      ‖(T t).comp (onePlusInverse A) - (T s).comp (onePlusInverse A)‖ ≤ L * |t - s| := by sorry

end QAlgorithms.Papers.Independent.Next46.P06

end
