-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_from_continuous_baire
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_from_continuous_baire
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:23:10.257748+00:00
-- url     : https://prove2.me/theorems/fff2e571-44c1-45a3-9fda-c8c1fb35580d
-- title:
--   Remark 6.6: continuous-to-Baire extension
-- statement:
--   Let $X$ be compact Hausdorff and let $L:C(X;k)\to L(H)$ be a unital $k$-linear star homomorphism. Let $\operatorname{Ba}(X)$ be the smallest sigma algebra making every continuous scalar-valued function measurable. Then
--
--   $$\exists!\ \Phi:M(X,\operatorname{Ba}(X))\to C(H)\text{ a measurable calculus extending }L.$$
--
--   Metrizability is not required. The conclusion concerns the Baire, not an arbitrary Borel, extension.
--
--   This is the continuous-to-Baire construction principle.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 28, Remark 6.6: continuous-to-Baire extension

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

/-- Remark 6.6, PDF p.28: a unique Baire, rather than arbitrary Borel, extension on a compact Hausdorff space. -/
theorem calculus_from_continuous_baire {Z : Type*} [TopologicalSpace Z] [CompactSpace Z] [T2Space Z]
    (L : C(Z, k) → H →L[k] H) (hL : ContinuousHom L) :
    ∃! F : @Symbol Z k (baire k Z) _ → Relation H,
      letI : MeasurableSpace Z := baire k Z
      Calculus F ∧ ∀ f, F (continuousBaireSymbol f) = boundedGraph (L f) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
