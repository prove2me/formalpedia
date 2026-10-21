-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_from_continuous_regular
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_from_continuous_regular
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:16:12.842394+00:00
-- url     : https://prove2.me/theorems/904dafaf-a9d0-4a3a-8d81-ce2f2b390706
-- title:
--   Theorem 6.4
-- statement:
--   Let $X$ be compact Hausdorff and let $L:C(X;k)\to L(H)$ be a unital $k$-linear star homomorphism. There is a unique measurable calculus $\Phi$ extending $L$ among those with the following regularity property: for every bounded nonnegative real-valued lower semicontinuous Borel $f$ and every $x\in H$,
--
--   $$\langle x,\Phi(f)x\rangle=\sup\{\langle x,L(g)x\rangle:g\in C_c(X;k),\ 0\le g\le f\}.$$
--
--   The functions under the supremum are real-valued. On compact $X$, every continuous function has compact support; the set contains zero and is bounded above. Pairings use the convention linear in the second entry. Uniqueness includes the displayed regularity condition.
--
--   This states the regular Borel extension principle without claiming unrestricted uniqueness.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 27, Theorem 6.4

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ENNReal InnerProductSpace

namespace QAlgorithms.Papers.Independent.Claimed50.P05

universe u v w

variable {k : Type*} [RCLike k]

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace k H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace k K] [CompleteSpace K]

/-- Theorem 6.4, PDF pp.27–28: uniqueness is restricted to extensions with the displayed regularity. -/
theorem calculus_from_continuous_regular [TopologicalSpace X] [BorelSpace X]
    [CompactSpace X] [T2Space X] (L : C(X, k) → H →L[k] H) (hL : ContinuousHom L) :
    ∃! F : Symbol X k → Relation H,
      Calculus F ∧ ExtendsContinuous F L ∧ RegularExtension F L := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
