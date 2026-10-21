-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P43_classicalExponentialStatistic
-- name    : QAlgorithms.Papers.Independent.Next46.P43.classicalExponentialStatistic
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:43:09.540042+00:00
-- url     : https://prove2.me/theorems/8b727970-ea90-44aa-91ad-d46fe683d194
-- title:
--   Unnumbered: sufficient and minimal statistic of a classical exponential family
-- statement:
--   Let $\mathcal P=(P_\theta)_{\theta\in\Theta}$ be a nonempty family of probabilities on $(X,\mathcal A)$. Suppose $\mu$ is sigma-finite, the real functions $T_1,\ldots,T_m$ and $h\geq0$ are measurable (nonnegativity may hold $\mu$-almost everywhere), and $\xi_i:\Theta\to\mathbb R$ are arbitrary coefficient functions. Assume $Z(\theta)=\int h\exp(\sum_i\xi_i(\theta)T_i)\,d\mu$ is finite and strictly positive and
--
--   $$
--   \frac{dP_\theta}{d\mu}=\frac{h\exp(\sum_i\xi_i(\theta)T_i)}{Z(\theta)}\quad\mu\text{-a.e.}
--   $$
--
--   Then $T=(T_1,\ldots,T_m)$ is sufficient. If $1,\xi_1,\ldots,\xi_m$ are linearly independent as real functions on $\Theta$, it is minimal sufficient: every set measurable for $T$ has one representative in any other sufficient sigma-algebra, equal almost everywhere under every $P_\theta$. Zero-weight support sectors and $m=0$ are permitted. This yields a minimal classical description when the coefficient functions are independent.
-- source:
--   Sufficiency in quantum statistical inference, arXiv:math-ph/0412093v1, PDF p. 21, Unnumbered: sufficient and minimal statistic of a classical exponential family

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P43

noncomputable section

open MeasureTheory Filter

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P43

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsTraceClass IsDensity State tensorApply productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (homogeneousEntropy generalizedRelativeEntropy traceFirst traceSecond)

/-- Unnumbered classical exponential statistic, PDF pp.20–21. Z is the actual
positive normalizing integral, h is nonnegative, and the density formula is
under the common dominating measure. Linear independence is of the constant
function and parameter coefficient functions on Theta, not functions on X.
Minimality is modulo common null sets; zero base-density sectors are allowed. -/
theorem classicalExponentialStatistic
    {X Theta : Type*} [MeasurableSpace X] [Nonempty Theta]
    (P : Theta → Measure X) (hProb : ∀ theta, IsProbabilityMeasure (P theta))
    (mu : Measure X) [SigmaFinite mu] {n : ℕ}
    (T : Fin n → X → ℝ) (hT : ∀ i, Measurable (T i))
    (xi : Theta → Fin n → ℝ) (h : X → ℝ) (hh : Measurable h)
    (hNonneg : ∀ᵐ x ∂mu, 0 ≤ h x) (Z : Theta → ℝ)
    (hPartition : ∀ theta,
      Integrable (fun x => Real.exp (∑ i, xi theta i * T i x) * h x) mu ∧
      Z theta = (∫ x, Real.exp (∑ i, xi theta i * T i x) * h x ∂mu) ∧
      0 < Z theta)
    (hDensity : ∀ theta, P theta = mu.withDensity
      (fun x => ENNReal.ofReal (ExponentialDensity T xi h Z theta x))) :
    SufficientSigmaAlgebra P (StatisticSigma T) ∧
      (LinearIndependent ℝ (show Option (Fin n) → (Theta → ℝ) from
        fun i theta => match i with | none => (1 : ℝ) | some j => xi theta j) →
        MinimalSufficientSigmaAlgebra P (StatisticSigma T)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P43

end
