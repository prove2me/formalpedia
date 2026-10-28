-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P02_stonean_of_monotoneComplete
-- name    : QAlgorithms.Papers.Independent.Renew46.P02.stonean_of_monotoneComplete
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T19:46:54.807488+00:00
-- url     : https://prove2.me/theorems/0a7f0da4-bed1-4fe7-8682-c9c5fc0e007d
-- title:
--   Lemma 5.3: Stonean space from monotone completeness
-- statement:
--   Let $K$ be a compact Hausdorff space. Assume every norm-bounded increasing net of positive elements of $C(K)$ has a supremum in its selfadjoint part. Then
--
--   $$
--   U\subseteq K\text{ open}\ \Longrightarrow\ \overline U\text{ open},\qquad
--   \overline{\operatorname{span}_{\mathbb C}\{p\in C(K):p=p^*=p^2\}}^{\|\cdot\|}=C(K).
--   $$
--
--   Thus $K$ is Stonean and its continuous projections span densely. Real continuous functions represent the selfadjoint part; nonempty directed subsets represent increasing nets, including the zero net.
-- source:
--   Abelian von Neumann algebras, measure algebras and L^\infty-spaces, arXiv:2108.06406v2, PDF p. 21, Lemma 5.3

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P02

noncomputable section

open MeasureTheory Set

open scoped ENNReal Topology CompactlySupported

namespace QAlgorithms.Papers.Independent.Renew46.P02

universe u v

/-- Lemma 5.3, PDF p.21. Real continuous functions model the selfadjoint
part; the projection span is complex and the closure is in norm. -/
theorem stonean_of_monotoneComplete (K : Type u) [TopologicalSpace K]
    [CompactSpace K] [T2Space K] (hmono : HasPositiveMonotoneSuprema K) :
    (∀ U : Set K, IsOpen U → IsOpen (closure U)) ∧
      (Submodule.span ℂ {f : C(K, ℂ) | IsStarProjection f}).topologicalClosure = ⊤ := by sorry

end QAlgorithms.Papers.Independent.Renew46.P02

end
