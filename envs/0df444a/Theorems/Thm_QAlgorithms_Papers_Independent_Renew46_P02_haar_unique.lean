-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P02_haar_unique
-- name    : QAlgorithms.Papers.Independent.Renew46.P02.haar_unique
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T19:50:03.76309+00:00
-- url     : https://prove2.me/theorems/43a6ccd3-6222-49d9-b724-917d79afb581
-- title:
--   Theorem 6.6: Uniqueness of Haar measure
-- statement:
--   Let $G$ be a locally compact Hausdorff topological group and let $\mu,\nu$ be nonzero left invariant Radon measures in Definition 6.4's complete, locally determined sense. Assume each domain is its measure's completed Borel sigma-algebra, as required immediately above the theorem. Then
--
--   $$
--   \Sigma_\mu=\Sigma_\nu,\qquad
--   \exists c\in\mathbb R,\ c>0:\ \mu(E)=c\nu(E)\quad(E\subseteq G).
--   $$
--
--   On arbitrary subsets the equation uses the associated outer measures, and on their common measurable domain it is equality of measures. The real scalar is finite and positive. This is Haar uniqueness with its completed domains identified.
-- source:
--   Abelian von Neumann algebras, measure algebras and L^\infty-spaces, arXiv:2108.06406v2, PDF p. 28, Theorem 6.6

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P02

noncomputable section

open MeasureTheory Set

open scoped ENNReal Topology CompactlySupported

namespace QAlgorithms.Papers.Independent.Renew46.P02

universe u v

/-- Theorem 6.6, PDF pp.28--29. Nonzero left invariant Fremlin Radon
measures on completed Borel domains have the same domain and differ
by a strictly positive finite real scalar. -/
theorem haar_unique {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (m0 m1 : MeasurableSpace G) (mu : @Measure G m0) (nu : @Measure G m1)
    (hmu : @IsFremlinRadon G _ m0 mu) (hnu : @IsFremlinRadon G _ m1 nu)
    (hdom0 : @HasCompletedBorelDomain G _ m0 mu)
    (hdom1 : @HasCompletedBorelDomain G _ m1 nu)
    (hnz0 : mu ≠ 0) (hnz1 : nu ≠ 0)
    (hinv0 : ∀ g : G, ∀ E : Set G, mu ((fun x => g * x) ⁻¹' E) = mu E)
    (hinv1 : ∀ g : G, ∀ E : Set G, nu ((fun x => g * x) ⁻¹' E) = nu E) :
    m0 = m1 ∧ ∃ c : ℝ, 0 < c ∧ ∀ E : Set G, mu E = ENNReal.ofReal c * nu E := by sorry

end QAlgorithms.Papers.Independent.Renew46.P02

end
