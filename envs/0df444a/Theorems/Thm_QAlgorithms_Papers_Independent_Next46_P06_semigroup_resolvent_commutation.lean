-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_semigroup_resolvent_commutation
-- name    : QAlgorithms.Papers.Independent.Next46.P06.semigroup_resolvent_commutation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:47:16.386611+00:00
-- url     : https://prove2.me/theorems/dc211027-0bbd-4215-8fbb-845a782ff8ec
-- title:
--   Corollary 13.2
-- statement:
--   Let $-A$ be the single-valued generator of a uniformly bounded semigroup $T$ on a complex Banach space, with $T(0)=I$ and strong continuity required only at positive times. For every bounded operator $S$,
--
--   $$S(I+A)^{-1}=(I+A)^{-1}S\iff\forall t>0,\ ST(t)=T(t)S.$$
--
--   This identifies the resolvent commutant with the positive-time semigroup commutant, without imposing dense generation.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 35, Corollary 13.2

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

/-- Corollary 13.2, PDF p.35: equality of the commutants of the positive-time
semigroup and of the resolvent (I+A)^(-1). -/
theorem semigroup_resolvent_commutation [CompleteSpace X] (T : ℝ → X →L[ℂ] X)
    (hT : BoundedSemigroup T) (hnd : NondegenerateSemigroup T)
    (S : X →L[ℂ] X) :
    let A := negativeGenerator T
    S.comp (onePlusInverse A) = (onePlusInverse A).comp S ↔
      ∀ t : ℝ, 0 < t → S.comp (T t) = (T t).comp S := by sorry

end QAlgorithms.Papers.Independent.Next46.P06

end
