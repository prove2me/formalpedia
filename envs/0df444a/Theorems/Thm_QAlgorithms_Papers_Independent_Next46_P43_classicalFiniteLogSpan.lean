-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P43_classicalFiniteLogSpan
-- name    : QAlgorithms.Papers.Independent.Next46.P43.classicalFiniteLogSpan
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T15:43:46.520495+00:00
-- url     : https://prove2.me/theorems/dd43d7fb-fe8c-48d2-b4c1-819316d52fe4
-- title:
--   Unnumbered: finite-dimensional log-density criterion for exponential families
-- statement:
--   Let $(P_\theta)_{\theta\in\Theta}$ be a nonempty family of probabilities, let $\mu$ be a sigma-finite common-support reference equivalent to each member, and let $r_\theta$ be measurable real versions of $dP_\theta/d\mu$, strictly positive $\mu$-almost everywhere. Write $[\log r_\theta]$ for their classes modulo $\mu$-null sets. Then
--
--   $$
--   \mathcal P\text{ admits a finite exponential-family representation}
--   \quad\Longleftrightarrow\quad
--   \dim_{\mathbb R}\operatorname{span}\{[\log r_\theta]:\theta\in\Theta\}<\infty.
--   $$
--
--   A finite exponential representation means measurable real statistics, parameter-dependent real coefficients, one measurable positive base density, and the finite positive normalizing integrals of the exponential densities, with the defining equalities holding almost everywhere. No boundedness or integrability of the logarithms is imposed. This is an existence criterion, rather than a prescribed number of statistics.
-- source:
--   Sufficiency in quantum statistical inference, arXiv:math-ph/0412093v1, PDF p. 21, Unnumbered: finite-dimensional log-density criterion for exponential families

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P43

noncomputable section

open MeasureTheory Filter

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P43

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsTraceClass IsDensity State tensorApply productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (homogeneousEntropy generalizedRelativeEntropy traceFirst traceSecond)

/-- Unnumbered logarithmic-span criterion, PDF p.21. The supplied measurable
r_theta are versions of the actual densities of P_theta with respect to the
sigma-finite common-support reference mu. Strict positivity almost everywhere
encodes mutual equivalence and prevents Real.log 0 from influencing the span.
The span consists of real functions modulo mu-null sets. No fixed number of
statistics, boundedness, or integrability of logarithms is assumed. -/
theorem classicalFiniteLogSpan
    {X Theta : Type*} [MeasurableSpace X] [Nonempty Theta]
    (P : Theta → Measure X) (hProb : ∀ theta, IsProbabilityMeasure (P theta))
    (mu : Measure X) [SigmaFinite mu] (r : Theta → X → ℝ)
    (hr : ∀ theta, Measurable (r theta))
    (hPositive : ∀ theta, ∀ᵐ x ∂mu, 0 < r theta x)
    (hDensity : ∀ theta, P theta =
      mu.withDensity (fun x => ENNReal.ofReal (r theta x))) :
    HasExponentialRepresentation mu r ↔
      FiniteDimensional ℝ (Submodule.span ℝ
        (Set.range (fun theta => LogDensityClass mu (r theta) (hr theta)))) := by sorry

end QAlgorithms.Papers.Independent.Next46.P43

end
