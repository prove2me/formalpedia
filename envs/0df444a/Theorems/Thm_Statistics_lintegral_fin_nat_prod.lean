-- Prove2me | Theorems.Thm_Statistics_lintegral_fin_nat_prod
-- name    : Statistics.lintegral_fin_nat_prod
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:32:12.5096+00:00
-- url     : https://prove2.me/theorems/c97782ea-29b9-4aa0-ae74-86646aea355a
-- title:
--   Tonelli for finite products: $\int \prod_i f_i(x_i) = \prod_i \int f_i$
-- statement:
--   **Tonelli's theorem for a finite product of measures.** Let $\mu_0,\dots,\mu_{n-1}$ be $\sigma$-finite measures on spaces $E_0,\dots,E_{n-1}$ and let $f_i : E_i \to [0,\infty]$ be measurable. Then the lower integral of the coordinatewise product against the product measure factorizes:
--   $$\int_{\prod_i E_i} \prod_{i} f_i(x_i)\; \mathrm{d}(\textstyle\bigotimes_i \mu_i)(x) \;=\; \prod_{i} \int_{E_i} f_i \,\mathrm{d}\mu_i .$$
--   No integrability hypothesis is needed: both sides are $[0,\infty]$-valued and the identity holds with the usual conventions. This is the $n$-variable form of the product rule $\int f\otimes g = \int f \int g$, obtained by iterating the two-variable Tonelli theorem along the measure-preserving equivalence $\prod_{i<n+1} E_i \cong E_0 \times \prod_{i<n} E_{i+1}$. Mathlib has the Bochner-integral and integrability versions (`integral_fintype_prod_eq_prod`, `Integrable.fintype_prod`) but not this one, which is the form needed whenever one must evaluate a product measure on a product of densities.
-- source:
--   L. Tonelli, Sull'integrazione per parti, Rend. Accad. Naz. Lincei 18 (1909), 246-253; textbook form: G. B. Folland, Real Analysis, 2nd ed., Wiley, 1999, Theorem 2.37 (Tonelli), iterated over a finite index set as in Section 2.6 (infinite product measures).

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

theorem Statistics.lintegral_fin_nat_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    {f : (i : Fin n) → E i → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ)
      = ∏ i, ∫⁻ y, f i y ∂(μ i) := by sorry
