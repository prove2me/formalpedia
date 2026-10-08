-- Prove2me | Theorems.Thm_SmithRegenerative_Moments_lemma_5_variance
-- name    : SmithRegenerative.Moments.lemma_5_variance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:34:59.379514+00:00
-- url     : https://prove2.me/theorems/63a80143-f0b8-4465-bcba-4dfcd4cf4cad
-- title:
--   Lemma 5 — variance of the overshoot reward
-- statement:
--   Suppose the cycle length $t_1$ and cycle reward $y_1$ have finite second moments. Write $\mu_1=\mathbb E t_1$, $\kappa_1=\mathbb E y_1$, $\sigma_1^2=\operatorname{var}(t_1)$, $\sigma_2^2=\operatorname{var}(y_1)$, and $c=\operatorname{cov}(t_1,y_1)$. Then $Y_t$ has a finite second moment for every $t\geq0$ and
--
--   $$
--   \operatorname{var}(Y_t)=\frac{t}{\mu_1}\left\{\sigma_2^2-2c\frac{\kappa_1}{\mu_1}+\sigma_1^2\left(\frac{\kappa_1}{\mu_1}\right)^2\right\}+o(t).
--   $$
--
--   This identifies the asymptotic variance coefficient later transferred from $Y_t$ to $w_t$.
--
--   **Formalization Note** The paper writes $\rho\sigma_1\sigma_2$ for $c$. Its final coefficient in (5·2·5) is printed as $\sigma_2^2$; Theorem 8 and the calculation require $\sigma_1^2$.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, p. 24, Lemma 5, (5·2·5); correction checked against p. 28, (5·3·7)

import Mathlib
import Definitions.Def_SmithRegenerative_Moments_CumulativeProcess

namespace SmithRegenerative.Moments

open MeasureTheory Filter

/-- Smith, *Regenerative stochastic processes*, Proc. R. Soc. Lond. A
232(1188):6–31 (1955), p. 24, Lemma 5, (5·2·5).
Formalization Note: the last printed `σ₂²` is a slip for `σ₁²`, as confirmed
by (5·3·7) on p. 28. `ρσ₁σ₂` is the length–reward covariance, which also
makes sense when either variance vanishes. Finite second moments make the
variance of each `Y_t` meaningful. -/
theorem lemma_5_variance {Ω : Type*} [MeasurableSpace Ω]
    (C : CumulativeProcess Ω)
    (hμ₂ : Integrable (fun ω => C.renewal.cycleLength 1 ω ^ 2) C.renewal.P)
    (hκ₂ : Integrable (fun ω => cycleReward C.renewal C.w 1 ω ^ 2) C.renewal.P) :
    (∀ t : ℝ, 0 ≤ t →
      Integrable (fun ω => C.overshootReward t ω ^ 2) C.renewal.P) ∧
    (fun t : ℝ =>
      ProbabilityTheory.variance (C.overshootReward t) C.renewal.P -
        t / C.meanLength *
          (ProbabilityTheory.variance (cycleReward C.renewal C.w 1) C.renewal.P -
            2 * C.lengthRewardCovariance * (C.meanReward / C.meanLength) +
            ProbabilityTheory.variance (C.renewal.cycleLength 1) C.renewal.P *
              (C.meanReward / C.meanLength) ^ 2))
      =o[atTop] (fun t : ℝ => t) := by sorry

end SmithRegenerative.Moments
