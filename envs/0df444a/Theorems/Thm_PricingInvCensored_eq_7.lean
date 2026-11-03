-- Prove2me | Theorems.Thm_PricingInvCensored_eq_7
-- name    : PricingInvCensored.eq_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:50:15.206915+00:00
-- url     : https://prove2.me/theorems/4b704190-a3de-411b-be46-4ab104561dde
-- title:
--   Eq. (7): $\mathbb E[(\varepsilon-z_p)^+]-\mathbb E[(\varepsilon-z_{p'})^+]=(z_{p'}-z_p)\Pr[\varepsilon\ge z_p]-\mathbb E[(z_{p'}-\varepsilon)\mathbf 1\{z_p\le\varepsilon\le z_{p'}\}]$
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R$ with finite mean, let $\varepsilon\sim\mu$, and let $z\le z'$. Then
--   $$\mathbb E[(\varepsilon-z)^+]-\mathbb E[(\varepsilon-z')^+]=\mathbb E\big[(\varepsilon-z)^+-(\varepsilon-z')^+\big]=(z'-z)\Pr[\varepsilon\ge z]-\mathbb E\big[(z'-\varepsilon)\mathbf 1\{z\le\varepsilon\le z'\}\big].$$
--
--   With $z=z_p$ and $z'=z_{p'}$ for prices $p<p'$, the left side is the unobservable part of $G(p')-G(p)$ (Eq. (6)), and the right side splits it into Part A, known up to $z_{p'}-z_p$, and Part B, estimable from censored leftovers.
--
--   Differences from the source:
--   - generalization: the noise law $\mu$ of Assumption 1 and $z_p<z_{p'}$ for $p<p'$ → any probability measure on $\mathbb R$ with finite mean and any $z\le z'$; reason: the identity holds for every such law and pair, and the source's case is $\mu$ with $z=z_p$, $z'=z_{p'}$.
-- source:
--   Chen, Wang & Zhou, Optimal Policies for Dynamic Pricing and Inventory Control with Nonparametric Censored Demands, SSRN 3750413 (2022-10-19), Eq. (7), p.15

import Mathlib

open MeasureTheory Set

namespace PricingInvCensored

/-- **Eq. (7)**, Chen, Wang & Zhou, SSRN 3750413 (2022-10-19), p.15. For a noise law `µ` with
finite mean and `z ≤ z′`,
`E[(ε − z)⁺] − E[(ε − z′)⁺] = E[(ε − z)⁺ − (ε − z′)⁺]
  = (z′ − z) Pr[ε ≥ z] − E[(z′ − ε) 1{z ≤ ε ≤ z′}]`.

**Formalization Note.** Stated for every probability measure on `ℝ` with integrable identity and
every `z ≤ z′`; the paper's case is `µ` of Assumption 1 and `z = z_p < z′ = z_{p′}`. -/
theorem eq_7 (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable (fun x : ℝ => x) μ)
    (z z' : ℝ) (hzz : z ≤ z') :
    (∫ ε, max (ε - z) 0 ∂μ) - (∫ ε, max (ε - z') 0 ∂μ) =
        ∫ ε, (max (ε - z) 0 - max (ε - z') 0) ∂μ ∧
      ∫ ε, (max (ε - z) 0 - max (ε - z') 0) ∂μ =
        (z' - z) * (μ (Ici z)).toReal - ∫ ε in Icc z z', (z' - ε) ∂μ := by sorry

end PricingInvCensored
