-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_from_continuous_metric
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_from_continuous_metric
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:16:42.131698+00:00
-- url     : https://prove2.me/theorems/4c23709f-4c87-491f-99b0-bc478f04a70d
-- title:
--   Corollary 6.5
-- statement:
--   Let $X$ be compact and metrizable, $H$ a Hilbert space, and $L:C(X;k)\to L(H)$ a unital $k$-linear star homomorphism. Then
--
--   $$\exists!\ \Phi:M(X,\operatorname{Bo}(X))\to C(H)\text{ a measurable calculus extending }L.$$
--
--   No extra regularity predicate is imposed in this uniqueness assertion.
--
--   This is unique continuous-to-Borel extension in the compact metrizable case.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 28, Corollary 6.5

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

/-- Corollary 6.5, PDF p.28: compact metrizability removes the extra uniqueness condition. -/
theorem calculus_from_continuous_metric [TopologicalSpace X] [BorelSpace X]
    [CompactSpace X] [TopologicalSpace.MetrizableSpace X] (L : C(X, k) → H →L[k] H) (hL : ContinuousHom L) :
    ∃! F : Symbol X k → Relation H, Calculus F ∧ ExtendsContinuous F L := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
