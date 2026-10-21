-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P02_normalRadon_nowhereDense_null
-- name    : QAlgorithms.Papers.Independent.Renew46.P02.normalRadon_nowhereDense_null
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T19:51:56.514199+00:00
-- url     : https://prove2.me/theorems/b632c088-f28a-4a4b-856b-801a4c6176d9
-- title:
--   Lemma 7.18: Normal Radon measures vanish on nowhere dense sets
-- statement:
--   Let $K$ be a compact Hausdorff Stonean space and $\mu$ a Radon probability measure in Definition 6.4's convention. Assume its integral functional on $C(K)$ is normal: it preserves suprema of norm-bounded increasing nets of nonnegative continuous functions whenever the supremum exists in $C(K)$. Then
--
--   $$
--   \operatorname{int}(\overline E)=\varnothing\ \Longrightarrow\ \mu^*(E)=0\qquad(E\subseteq K).
--   $$
--
--   Thus every nowhere dense subset is null, including subsets whose measurability was not assumed. Normality is the proof-used hypothesis omitted from the printed lemma; this corrected reading requires independent moderation.
-- source:
--   Abelian von Neumann algebras, measure algebras and L^\infty-spaces, arXiv:2108.06406v2, PDF p. 36, Lemma 7.18

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P02

noncomputable section

open MeasureTheory Set

open scoped ENNReal Topology CompactlySupported

namespace QAlgorithms.Papers.Independent.Renew46.P02

universe u v

/-- Lemma 7.18, PDF p.36, corrected to its proof's reading: normality
of the integral is necessary but omitted in print. Every nowhere dense
subset has outer measure zero. Independent moderation of this correction is pending. -/
theorem normalRadon_nowhereDense_null {K : Type u} [TopologicalSpace K]
    [CompactSpace K] [T2Space K] [MeasurableSpace K] (mu : Measure K)
    (hrad : IsFremlinRadon mu) (hprob : mu Set.univ = 1)
    (hstone : ∀ U : Set K, IsOpen U → IsOpen (closure U))
    (hnormal : HasNormalContinuousIntegral mu) (E : Set K)
    (hE : interior (closure E) = ∅) : mu E = 0 := by sorry

end QAlgorithms.Papers.Independent.Renew46.P02

end
