-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P02_riesz_compactDecomposition
-- name    : QAlgorithms.Papers.Independent.Renew46.P02.riesz_compactDecomposition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T19:48:10.433643+00:00
-- url     : https://prove2.me/theorems/21d0bc92-b761-4173-bb49-40b409256f5e
-- title:
--   Theorem 6.2: Compact decomposition of the Riesz measure extension
-- statement:
--   Let $X$ be locally compact Hausdorff and $I$ a positive complex linear functional on $C_c(X,\mathbb C)$. Let $\mu_0$ and its outer extension $\mu_0^*$ be constructed from $I$ by the open-set supremum, open-envelope infimum, compact inner supremum, and Borel-envelope infimum on pp.22–23. Let $\mathcal M$ be the Caratheodory domain of $\mu_0^*$. Then $(X,\mathcal M,\mu_0^*)$ is decomposable. There is a pairwise disjoint family $\mathcal C$ of compact sets such that each $K\in\mathcal C$ has $\mu_0(K)>0$, every open $U$ meeting $K$ has $\mu_0(U\cap K)>0$, and every compact $K_0$ meets only countably many members of $\mathcal C$. In addition,
--
--   $$
--   \mu_0^*(E)=\sum_{K\in\mathcal C}\mu_0^*(E\cap K)\quad(E\in\mathcal M),
--   \qquad
--   E\in\mathcal M\iff \forall K\in\mathcal C,\ E\cap K\in\mathcal M.
--   $$
--
--   Every subset of $N=X\setminus\bigcup\mathcal C$ is $\mu_0^*$-null. Decomposability means a measurable finite-measure partition of the whole space, with piecewise measurability and the displayed sum formula; the remaining null part is included. The family may be empty when $I=0$.
-- source:
--   Abelian von Neumann algebras, measure algebras and L^\infty-spaces, arXiv:2108.06406v2, PDF p. 25, Theorem 6.2

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P02

noncomputable section

open MeasureTheory Set

open scoped ENNReal Topology CompactlySupported

namespace QAlgorithms.Papers.Independent.Renew46.P02

universe u v

/-- Theorem 6.2, PDF pp.25--27. All five compact-family properties and
whole-space decomposability are retained, including the remaining null part. -/
theorem riesz_compactDecomposition {X : Type u} [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] (I : C_c(X, ℂ) →ₗ[ℂ] ℂ)
    (hI : IsPositiveRieszFunctional I) :
    IsDecomposableDomain (IsCaratheodorySet (rieszExtension I)) (rieszExtension I) ∧
    ∃ C : Set (Set X), C.Pairwise Disjoint ∧
      (∀ K ∈ C, IsCompact K ∧ 0 < rieszBorelPart I K) ∧
      (∀ U : Set X, IsOpen U → ∀ K ∈ C,
        (U ∩ K).Nonempty → 0 < rieszBorelPart I (U ∩ K)) ∧
      (∀ K0 : Set X, IsCompact K0 → {K ∈ C | (K0 ∩ K).Nonempty}.Countable) ∧
      (∀ E : Set X, IsCaratheodorySet (rieszExtension I) E →
        rieszExtension I E = ∑' K : C, rieszExtension I (E ∩ K.val)) ∧
      (∀ E : Set X, IsCaratheodorySet (rieszExtension I) E ↔
        ∀ K ∈ C, IsCaratheodorySet (rieszExtension I) (E ∩ K)) ∧
      (∀ E : Set X, E ⊆ (Set.sUnion C)ᶜ → rieszExtension I E = 0) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P02

end
