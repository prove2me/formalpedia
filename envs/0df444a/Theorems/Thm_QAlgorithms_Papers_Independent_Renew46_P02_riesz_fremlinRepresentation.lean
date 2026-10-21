-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P02_riesz_fremlinRepresentation
-- name    : QAlgorithms.Papers.Independent.Renew46.P02.riesz_fremlinRepresentation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T19:52:53.324804+00:00
-- url     : https://prove2.me/theorems/6a5ef113-2d11-4f74-93ca-64d08583c823
-- title:
--   Unnumbered Riesz representation in the six-clause Radon convention
-- statement:
--   Let $X$ be locally compact Hausdorff. Positive complex linear functionals $I$ on $C_c(X,\mathbb C)$ correspond bijectively to Radon measures in the six-clause convention of Definition 6.4. Construct $\mu_0^*$ from $I$ by the open-set supremum, open-envelope infimum, compact inner supremum and Borel-envelope infimum of pp.22–23, and let $\mathcal M_{\mu_0^*}$ be its Caratheodory domain. The representing measure satisfies
--
--   $$
--   \Sigma=\mathcal M_{\mu_0^*},\qquad
--   \mu(E)=\mu_0^*(E)\ (E\subseteq X),\qquad
--   I(f)=\int_X f\,d\mu\ (f\in C_c(X,\mathbb C)).
--   $$
--
--   Every such $f$ is integrable. The measure and its entire domain are unique among six-clause Radon realizations. Conversely every six-clause Radon measure induces such a functional and equals its canonical extension on the same complete domain. This retains the full-domain correspondence beyond agreement only on Borel sets.
-- source:
--   Abelian von Neumann algebras, measure algebras and L^\infty-spaces, arXiv:2108.06406v2, PDF p. 27, Unnumbered Riesz representation in the six-clause Radon convention

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P02

noncomputable section

open MeasureTheory Set

open scoped ENNReal Topology CompactlySupported

namespace QAlgorithms.Papers.Independent.Renew46.P02

universe u v

/-- Full-domain Riesz bijection, unnumbered statement, PDF p.27,
construction pp.22--23. Both domains and outer values are identified. -/
theorem riesz_fremlinRepresentation {X : Type u} [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] :
    (∀ I : C_c(X, ℂ) →ₗ[ℂ] ℂ, IsPositiveRieszFunctional I →
      ∃ m : MeasurableSpace X, ∃ mu : @Measure X m,
        @IsFremlinRadon X _ m mu ∧
        (∀ E : Set X, MeasurableSet[m] E ↔ IsCaratheodorySet (rieszExtension I) E) ∧
        (∀ E : Set X, mu E = rieszExtension I E) ∧
        (∀ f : C_c(X, ℂ), Integrable (fun x => f x) mu ∧ (∫ x, f x ∂mu) = I f) ∧
        (∀ n : MeasurableSpace X, ∀ nu : @Measure X n,
          @IsFremlinRadon X _ n nu →
          (∀ f : C_c(X, ℂ), Integrable (fun x => f x) nu ∧ (∫ x, f x ∂nu) = I f) →
          n = m ∧ ∀ E : Set X, nu E = mu E)) ∧
    (∀ m : MeasurableSpace X, ∀ mu : @Measure X m, @IsFremlinRadon X _ m mu →
      ∃ I : C_c(X, ℂ) →ₗ[ℂ] ℂ, IsPositiveRieszFunctional I ∧
        (∀ f : C_c(X, ℂ), Integrable (fun x => f x) mu ∧ (∫ x, f x ∂mu) = I f) ∧
        (∀ E : Set X, MeasurableSet[m] E ↔ IsCaratheodorySet (rieszExtension I) E) ∧
        ∀ E : Set X, mu E = rieszExtension I E) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P02

end
