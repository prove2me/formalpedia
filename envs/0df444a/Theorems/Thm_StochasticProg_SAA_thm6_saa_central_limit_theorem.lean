-- Prove2me | Theorems.Thm_StochasticProg_SAA_thm6_saa_central_limit_theorem
-- name    : StochasticProg.SAA.thm6_saa_central_limit_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T20:14:13.732985+00:00
-- url     : https://prove2.me/theorems/f460614f-20cd-4e45-8c72-9b674a63b929
-- title:
--   Chapter 9, Theorem 6 — central limit theorem for the SAA optimal value
-- statement:
--   **Chapter 9, Theorem 6** (Birge & Louveaux, p. 411; Shapiro [1991, Theorem 3.3]): a central
--   limit theorem for the optimal value of the sample average approximation (SAA).
--
--   Fix a compact set $X$ of feasible first-stage decisions in $\mathbb R^n$, a measurable space
--   $(\Xi,\mathcal B)$ of random-parameter outcomes, and an integrand $g:\mathbb R^n\times\Xi\to
--   \mathbb R$ with $g(x,\cdot)$ measurable for every $x\in X$. Let $\xi_1,\xi_2,\dots$ be an
--   i.i.d. sample from a common law $\mu$ on $(\Xi,\mathcal B)$ (formalized as a sequence
--   $\xi:\mathbb N\to\Omega\to\Xi$ on an ambient probability space $(\Omega,P)$, independent and
--   identically distributed with law $\mu$). Suppose there is $a:\Xi\to\mathbb R$ with
--   $\int_\Xi a(\xi)^2\,\mu(d\xi)<\infty$ such that
--   $$
--   |g(x_1,\xi)-g(x_2,\xi)|\le a(\xi)\,\|x_1-x_2\| \qquad (x_1,x_2\in X,\ \xi\in\Xi),
--   $$
--   and suppose $x_0\in X$ is the **unique** minimizer of $x\mapsto \mathbb E\,g(x) :=
--   \int_\Xi g(x,\xi)\,\mu(d\xi)$ over $X$ (with $\int_\Xi g(x_0,\xi)\,\mu(d\xi)$ finite). Let
--   $z_\nu(\omega)$ be the optimal value of the size-$\nu$ SAA problem at sample outcome $\omega$,
--   $$
--   z_\nu(\omega) = \min_{x\in X} \frac1\nu\sum_{i=1}^\nu g(x,\xi_i(\omega)) .
--   $$
--   Then
--   $$
--   \sqrt\nu\,\bigl[z_\nu - \mathbb E\,g(x_0)\bigr] \xrightarrow{d} N\bigl(0,\ \mathrm{Var}\,
--   g(x_0)\bigr) ,
--   $$
--   i.e. $\sqrt\nu(z_\nu-z^*)$ converges in distribution to a centered Gaussian of variance
--   $\mathrm{Var}\,g(x_0) = \int_\Xi g(x_0,\xi)^2\,\mu(d\xi) - \bigl(\int_\Xi
--   g(x_0,\xi)\,\mu(d\xi)\bigr)^2$, where $z^*=\mathbb E\,g(x_0)$ is the true optimal value (since
--   $x_0$ is optimal).
--
--   This is a genuinely hard result — a functional/uniform-convergence argument over the whole
--   feasible set $X$, not the plain i.i.d. central limit theorem at the single point $x_0$ — and
--   the book states it without proof, citing Shapiro [1991]. It motivates the exponential-rate
--   result of Theorem 7 (the mission goal), which replaces the CLT's asymptotic normal
--   approximation by an explicit finite-sample tail bound under stronger moment hypotheses.
--
--   **Formalization Note** Convergence in distribution is Mathlib's `TendstoInDistribution`: the
--   laws of $\sqrt\nu[z_\nu-\mathbb Eg(x_0)]$ (as probability measures on $\mathbb R$) converge
--   weakly to the law of an explicitly supplied random variable `Y` with `HasLaw Y (gaussianReal 0
--   (Var[g x0; μ]).toNNReal) P'` on a separate probability space `(Ω', P')` — the same pattern
--   Mathlib's own i.i.d. central limit theorem (`ProbabilityTheory.
--   tendstoInDistribution_inv_sqrt_mul_sum_sub`) uses for its conclusion, confirming the target
--   notion of convergence is the right one for a faithful statement of this theorem. `zSAA ν ω` is
--   an SAA optimal *value*, characterized as a lower bound attained at some `x ∈ X` (an `IsLeast`-
--   style pair of hypotheses `hSAA`/`hSAA_attain`), not `sInf` of an image set directly, since `X`
--   is only assumed compact (not the whole feasible-value set shown bounded a priori) and `Real.
--   sInf` returns a junk value `0` on an unbounded-below or empty set (trap 5 of
--   `reference/FAITHFULNESS_TRAPS.md`); the explicit lower-bound-plus-attainment pair sidesteps
--   that junk value entirely. `x0`'s uniqueness is stated as a strict-inequality hypothesis
--   (`hx0uniq`) rather than a bare `IsLeast`/injectivity pairing, matching the book's "has a unique
--   minimizer" directly. The `L²`-envelope `a` majorizing `g`'s Lipschitz constant is existentially
--   supplied (as the book's hypothesis (ii) states), not derived.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, p. 411, Chapter 9, Theorem 6

import Mathlib

namespace StochasticProg.SAA

open MeasureTheory ProbabilityTheory

variable {n : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]

/-- Chapter 9, Theorem 6 (Birge & Louveaux, p. 411; Shapiro [1991, Theorem 3.3]): the central
limit theorem for the sample average approximation (SAA) optimal value. `X` is compact; `g` is
the (abstract) integrand, measurable in `ξ` for every `x ∈ X`, Lipschitz in `x` with an
`L²`-envelope `a`; `μ` is the common law of the i.i.d. sample `ξ : ℕ → Ω → Ξ`; `x0` is the unique
minimizer of `x ↦ E g(x)` over `X`; `zSAA ν ω` is the optimal value of the size-`ν` SAA problem.
The conclusion is that `√ν·(zSAA ν - z0)` converges in distribution to a centered Gaussian of
variance `Var g(x0)`, matching the book's `N(0, Var g(x0))`; `z0` is the value `E g(x0)`, i.e. the
optimum of the true problem (5.1) since `x0` is optimal. -/
theorem thm6_saa_central_limit_theorem
    (X : Set (EuclideanSpace ℝ (Fin n))) (g : EuclideanSpace ℝ (Fin n) → Ξ → ℝ)
    (hXcompact : IsCompact X)
    (hgmeas : ∀ x ∈ X, Measurable (g x))
    (P : Measure Ω) [IsProbabilityMeasure P] (ξ : ℕ → Ω → Ξ)
    (hindep : iIndepFun ξ P) (hident : ∀ i, IdentDistrib (ξ i) (ξ 0) P P)
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (hμ : HasLaw (ξ 0) μ P)
    (a : Ξ → ℝ) (ha2 : MemLp a 2 μ)
    (hlip : ∀ x1 ∈ X, ∀ x2 ∈ X, ∀ ξ' : Ξ, |g x1 ξ' - g x2 ξ'| ≤ a ξ' * ‖x1 - x2‖)
    (x0 : EuclideanSpace ℝ (Fin n)) (hx0mem : x0 ∈ X)
    (hx0int : Integrable (g x0) μ)
    (hx0uniq : ∀ x ∈ X, x ≠ x0 → (∫ ξ', g x0 ξ' ∂μ) < ∫ ξ', g x ξ' ∂μ)
    (zSAA : ℕ → Ω → ℝ)
    (hSAA : ∀ (ν : ℕ) (ω : Ω), ∀ x ∈ X, zSAA ν ω ≤ (ν : ℝ)⁻¹ * ∑ i ∈ Finset.range ν, g x (ξ i ω))
    (hSAA_attain : ∀ (ν : ℕ) (ω : Ω), ∃ x ∈ X,
      (ν : ℝ)⁻¹ * ∑ i ∈ Finset.range ν, g x (ξ i ω) = zSAA ν ω)
    (hzSAA_meas : ∀ ν, Measurable (zSAA ν))
    (Ω' : Type*) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → ℝ) (hY : HasLaw Y (gaussianReal 0 (Var[g x0; μ]).toNNReal) P') :
    TendstoInDistribution (fun (ν : ℕ) ω => Real.sqrt (ν : ℝ) * (zSAA ν ω - ∫ ξ', g x0 ξ' ∂μ))
      Filter.atTop Y (fun _ => P) P' := by sorry

end StochasticProg.SAA
