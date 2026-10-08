-- Prove2me | Theorems.Thm_SmithRegenerative_Equilibrium_lemma_A
-- name    : SmithRegenerative.Equilibrium.lemma_A
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:30:16.642307+00:00
-- url     : https://prove2.me/theorems/35491883-b87e-4bf3-91f4-da7e5a21fc18
-- title:
--   Lemma A — for F ∈ 𝔖, (1 − G*(s))/(1 − F*(s)) is the Laplace–Stieltjes transform of a bounded-variation Ω with Ω(+∞) − Ω(0−) = λ₁/μ₁
-- statement:
--   Let $F$ and $G$ be laws of non-negative random variables with finite positive means $\mu_1$ and $\lambda_1$, and suppose $F \in \mathfrak S$. Write $F^*(s) = \int_{0-}^\infty e^{-st}\, dF(t)$ for the Laplace–Stieltjes transform (2·2·4). Then there is a function $\Omega$ of bounded total variation with $\Omega(t) = 0$ for $t < 0$ whose Laplace–Stieltjes transform is, for $\Re(s) > 0$,
--   $$
--   \int_{0-}^\infty e^{-st}\, d\Omega(t) = \frac{1 - G^*(s)}{1 - F^*(s)},
--   $$
--   and $\Omega(+\infty) - \Omega(0-) = \lambda_1/\mu_1$.
--
--   The lemma (Smith 1954, lemmas 5 and 6) is the analytic tool in the proof of Theorem 1: with $G$ exponential it identifies the transform of the renewal integral as that of a convolution with a function of bounded variation.
--
--   **Formalization Note** $\Omega$ is represented by its Lebesgue–Stieltjes signed measure, written as $\nu_1 - \nu_2$ with $\nu_1, \nu_2$ finite measures on $[0,\infty)$; its transform is $\int e^{-st}\,d\nu_1 - \int e^{-st}\,d\nu_2$ and $\Omega(+\infty) - \Omega(0-) = \nu_1(\mathbb R) - \nu_2(\mathbb R)$. The transform `lst` is that of the referenced definition `QueueingFundamentals.MG1.transforms` and includes an atom at $0$, as $\int_{0-}$ does.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, p. 11, Lemma A (with (2·2·4), p. 10)

import Mathlib
import Definitions.Def_SmithRegenerative_Equilibrium_Renewal

namespace SmithRegenerative.Equilibrium

open MeasureTheory QueueingFundamentals.MG1

/-- **Lemma A** (Smith 1955, §2·2, p. 11; lemmas 5, 6 of Smith 1954). Let `F` and `G` be laws of
non-negative random variables with finite positive means `μ₁` and `λ₁`, and let `F ∈ 𝔖`. Then there
is a function `Ω(t)` of bounded total variation, with `Ω(t) = 0` for `t < 0`, whose
Laplace–Stieltjes transform is `(1 − G*(s))/(1 − F*(s))` for `ℜ(s) > 0`, and
`Ω(+∞) − Ω(0−) = λ₁/μ₁`. Here `F*(s) = ∫_{0−}^∞ e^{−st} dF(t)` (2·2·4).

Formalization Note: a function of bounded total variation vanishing on `(−∞, 0)` is represented by
its Lebesgue–Stieltjes signed measure, written as a difference `ν₁ − ν₂` of two finite measures
concentrated on `[0, ∞)` (Jordan decomposition). Its Laplace–Stieltjes transform
`∫_{0−}^∞ e^{−st} dΩ(t)` is `lst ν₁ s − lst ν₂ s`, and `Ω(+∞) − Ω(0−)` is `ν₁(ℝ) − ν₂(ℝ)`.
`lst μ s = ∫ e^{−st} dμ(t)` is from the referenced `QueueingFundamentals.MG1.transforms`; it
includes an atom at `0`, as `∫_{0−}` does. -/
theorem lemma_A (F G : Measure ℝ) [IsProbabilityMeasure F] [IsProbabilityMeasure G]
    (hF0 : F (Set.Iio 0) = 0) (hG0 : G (Set.Iio 0) = 0)
    (hFpos : 0 < mean F) (hFfin : mean F < ⊤) (hGpos : 0 < mean G) (hGfin : mean G < ⊤)
    (hS : InClassS F) :
    ∃ ν₁ ν₂ : Measure ℝ, IsFiniteMeasure ν₁ ∧ IsFiniteMeasure ν₂ ∧
      ν₁ (Set.Iio 0) = 0 ∧ ν₂ (Set.Iio 0) = 0 ∧
      (∀ s : ℂ, 0 < s.re → lst ν₁ s - lst ν₂ s = (1 - lst G s) / (1 - lst F s)) ∧
      (ν₁ Set.univ).toReal - (ν₂ Set.univ).toReal = (mean G).toReal / (mean F).toReal := by sorry

end SmithRegenerative.Equilibrium
