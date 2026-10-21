-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P09_finiteRank_perturbationDomain
-- name    : QAlgorithms.Papers.Independent.Next46.P09.finiteRank_perturbationDomain
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:05:13.851457+00:00
-- url     : https://prove2.me/theorems/7bde0c4a-93f1-4fc7-9a85-8358a8f1b849
-- title:
--   Finite-rank perturbations preserve the full generator domain
-- statement:
--   Let $L^0$ be the actual generator of a dynamical semigroup on the full complex trace class $\mathcal T(H)$ of a separable complete complex Hilbert space. Let $P:\operatorname{dom}L^0\to\mathcal T(H)$ be a complex linear completely positive perturbation satisfying $\operatorname{tr}P(\rho)\le-\operatorname{tr}L^0(\rho)$ for positive $\rho$ in its domain. Let $L$ be the actual generator of the minimal semigroup obtained from the resolvent series in Proposition II.4. If the image of the map $P$ spans a finite-dimensional complex vector space, then
--
--   $$\operatorname{dom}L=\operatorname{dom}L^0.$$
--
--   Finite rank concerns the perturbation map, rather than the operator ranks of individual outputs. No additional relative bound below one is assumed. This result identifies precisely the unchanged full domain for finite-rank reset perturbations.
-- source:
--   Unbounded generators of dynamical semigroups, arXiv:1707.02266v1, PDF p. 9, Lemma II.5: finite-rank perturbations preserve domains

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P09

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Next46.P09

universe u v

open QAlgorithms.Papers.Independent.Dependency50.P13
  (TraceClass IsTraceClass traceNormValue operatorTrace IsPositive)

open QAlgorithms.Papers.Independent.Claimed50.P50 (ContractionSemigroup)

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H]

/-- Lemma II.5, arXiv:1707.02266v1, PDF p.9.
The minimal semigroup is the actual construction in Proposition II.4.
There is no extra relative-norm bound smaller than one. -/
theorem finiteRank_perturbationDomain [TopologicalSpace.SeparableSpace H]
    {I : Type v} (b : HilbertBasis I ℂ H)
    (Tzero : TraceDynamicalSemigroup b) (P : DomainPerturbation Tzero)
    (T : TraceDynamicalSemigroup b) (hMinimal : IsMinimalPerturbation Tzero P T)
    (hFinite : FiniteDimensional ℂ (PerturbationRange P)) :
    TraceGeneratorDomain T = TraceGeneratorDomain Tzero := by sorry

end QAlgorithms.Papers.Independent.Next46.P09

end
