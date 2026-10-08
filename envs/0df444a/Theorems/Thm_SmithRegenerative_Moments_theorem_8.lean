-- Prove2me | Theorems.Thm_SmithRegenerative_Moments_theorem_8
-- name    : SmithRegenerative.Moments.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:35:43.248212+00:00
-- url     : https://prove2.me/theorems/07a06945-0ac8-4dfd-a51e-9f91423d4399
-- title:
--   Theorem 8 — mean and variance of a cumulative process
-- statement:
--   Let $w_t$ be a cumulative process. Write $\mu_1=\mathbb E t_1$, $\kappa_1=\mathbb E y_1$, $\sigma_1^2=\operatorname{var}(t_1)$, $\sigma_2^2=\operatorname{var}(y_1)$, and $c=\operatorname{cov}(t_1,y_1)$. If the cycle length and first cycle variation are integrable, then $w_t$ is integrable for every $t\geq0$ and
--
--   $$
--   \mathbb E w_t=\frac{\kappa_1}{\mu_1}t+o(t).
--   $$
--
--   If, in addition, the cycle length and first cycle variation have finite second moments, then $w_t$ has a finite second moment for every $t\geq0$ and
--
--   $$
--   \operatorname{var}(w_t)=\frac{t}{\mu_1}\left\{\sigma_2^2-2c\frac{\kappa_1}{\mu_1}+\sigma_1^2\left(\frac{\kappa_1}{\mu_1}\right)^2\right\}+o(t),\qquad t\to\infty.
--   $$
--
--   These formulas extend renewal-reward asymptotics from completed-cycle sums to the process observed at an arbitrary time.
--
--   **Formalization Note** The paper writes $\rho\sigma_1\sigma_2$ for $c$; covariance also gives the intended value when a cycle variance is zero. The limit is along real time.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, p. 28, Theorem 8(i)–(ii), (5·3·6)–(5·3·7)

import Mathlib
import Definitions.Def_SmithRegenerative_Moments_CumulativeProcess

namespace SmithRegenerative.Moments

open MeasureTheory Filter

/-- Smith, *Regenerative stochastic processes*, Proc. R. Soc. Lond. A
232(1188):6–31 (1955), p. 28, Theorem 8(i)–(ii), (5·3·6)–(5·3·7).
Formalization Note: `ρσ₁σ₂` is represented by covariance, preserving
within-cycle length–reward dependence and covering zero-variance cases.
Square-integrability of `w_t` is a conclusion under the second-moment
hypotheses, preventing Lean's real-variance zero default on infinite values. -/
theorem theorem_8 {Ω : Type*} [MeasurableSpace Ω]
    (C : CumulativeProcess Ω)
    (hμ : Integrable (C.renewal.cycleLength 1) C.renewal.P)
    (hvar : Integrable (cycleVariation C.renewal C.w 1) C.renewal.P) :
    ((∀ t : ℝ, 0 ≤ t → Integrable (C.w t) C.renewal.P) ∧
      (fun t : ℝ =>
        (∫ ω, C.w t ω ∂C.renewal.P) -
          C.meanReward / C.meanLength * t) =o[atTop] (fun t : ℝ => t)) ∧
    (Integrable (fun ω => C.renewal.cycleLength 1 ω ^ 2) C.renewal.P →
      Integrable (fun ω => cycleVariation C.renewal C.w 1 ω ^ 2) C.renewal.P →
      (∀ t : ℝ, 0 ≤ t → Integrable (fun ω => C.w t ω ^ 2) C.renewal.P) ∧
      (fun t : ℝ =>
        ProbabilityTheory.variance (C.w t) C.renewal.P -
          t / C.meanLength *
            (ProbabilityTheory.variance (cycleReward C.renewal C.w 1) C.renewal.P -
              2 * C.lengthRewardCovariance * (C.meanReward / C.meanLength) +
              ProbabilityTheory.variance (C.renewal.cycleLength 1) C.renewal.P *
                (C.meanReward / C.meanLength) ^ 2))
        =o[atTop] (fun t : ℝ => t)) := by sorry

end SmithRegenerative.Moments
