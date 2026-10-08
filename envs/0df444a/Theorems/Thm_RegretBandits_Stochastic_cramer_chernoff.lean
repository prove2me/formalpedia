-- Prove2me | Theorems.Thm_RegretBandits_Stochastic_cramer_chernoff
-- name    : RegretBandits.Stochastic.cramer_chernoff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:19:31.007081+00:00
-- url     : https://prove2.me/theorems/98f3f75b-8b70-4961-ba0b-f450ddb95e35
-- title:
--   Eq. (2.3) — Cramér–Chernoff bound $\mathbb P(\mu_i-\hat\mu_{i,s}>\varepsilon)\le e^{-s\psi^*(\varepsilon)}$
-- statement:
--   Consider a stochastic bandit whose reward distributions satisfy the moment condition (2.2) with a convex function $\psi$, and let $\psi^*(\varepsilon)=\sup_{\lambda\in\mathbb R}(\lambda\varepsilon-\psi(\lambda))$. Let $\hat\mu_{i,s}$ be the sample mean of the first $s\ge1$ rewards of arm $i$. Then for every $\varepsilon\ge0$,
--   $$\mathbb P\big(\mu_i-\hat\mu_{i,s}>\varepsilon\big)\le e^{-s\,\psi^*(\varepsilon)},$$
--   with $e^{-\infty}=0$.
--
--   This concentration inequality is what makes $\hat\mu_{i,s}+(\psi^*)^{-1}(\frac1s\ln\frac1\delta)$ an upper confidence bound on $\mu_i$ at level $1-\delta$; the UCB analysis applies it with a union bound over the number of pulls.
--
--   **Formalization Note.** Two conventions the book leaves implicit are stated. (i) $\varepsilon\ge0$: for $\varepsilon<0$ the printed inequality is false (with $\psi(\lambda)=\lambda^2/8$ it would bound a probability close to $1$ by $e^{-2s\varepsilon^2}$). (ii) $\psi(\lambda)\ge\psi(0)$ for $\lambda\le0$. Condition (2.2) constrains $\psi$ only on $\lambda\ge0$, while $\psi^*$ takes the supremum over all $\lambda\in\mathbb R$. Without (ii), $\psi(\lambda)=c\lambda+\lambda^2/8$ with large $c>0$ satisfies (2.2) for $[0,1]$ rewards and has $\psi^*(\varepsilon)=2(\varepsilon-c)^2$, which makes (2.3) false for small $\varepsilon$. Every $\psi$ used in the book is even and satisfies (ii). Under (ii) the supremum may be taken over $\lambda\ge0$. $\psi^*$ is computed in the extended reals and the right side is the extended exponential.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 10, Eq. (2.3)

import Mathlib
import Definitions.Def_RegretBandits_Stochastic_model

namespace RegretBandits.Stochastic

open MeasureTheory

/-- Eq. (2.3) of Bubeck and Cesa-Bianchi (arXiv:1204.5721v2, p. 10): if the rewards satisfy
(2.2) with a convex `ψ` (which is not below `ψ 0` on `(-∞, 0]`), then for every arm `i`, every
number of pulls `s ≥ 1` and every `ε ≥ 0`,
`ℙ(μ_i - μ̂_{i,s} > ε) ≤ e^{-s ψ*(ε)}`, with `e^{-∞} = 0`. -/
theorem cramer_chernoff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {K : ℕ} (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ)
    (hX : IsStochasticBandit P X μ) (ψ : ℝ → ℝ) (hψ : SatisfiesMomentCondition P ψ X μ)
    (hψneg : ∀ l : ℝ, l ≤ 0 → ψ 0 ≤ ψ l) (i : Fin K) (s : ℕ) (hs : 1 ≤ s) (ε : ℝ)
    (hε : 0 ≤ ε) :
    P {ω | ε < μ i - sampleMean X i s ω} ≤
      EReal.exp (-((s : ℝ) : EReal) * legendreFenchel ψ ε) := by sorry

end RegretBandits.Stochastic
