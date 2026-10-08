-- Prove2me | Theorems.Thm_SAARate_Polyhedral_pointwise_exponential_bounds
-- name    : SAARate.Polyhedral.pointwise_exponential_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:19.884238+00:00
-- url     : https://prove2.me/theorems/06a98e4c-4501-4287-a9a6-321503ac0c2b
-- title:
--   p. 13, proof of Theorem 3.2 — both tails of f̂_N(x) − f(x) decay exponentially in N
-- statement:
--   Let $\Omega$ be finite, $P$ a probability measure on $\Omega$, $h:\mathbb R^m\times\Omega\to\mathbb R$, and $\omega^1,\omega^2,\dots$ an i.i.d. sample from $P$ on a probability space $(S,Q)$. Fix $x\in\mathbb R^m$ and $\varepsilon>0$. Then there are $\beta_1>0$ and $\beta_2>0$ with
--   $$
--   \limsup_{N\to\infty}\frac1N\log Q\big(\hat f_N(x)\ge f(x)+\varepsilon\big)\le-\beta_1,\qquad
--   \limsup_{N\to\infty}\frac1N\log Q\big(\hat f_N(x)\le f(x)-\varepsilon\big)\le-\beta_2 .
--   $$
--
--   Here $\hat f_N(x)$ is the mean of $N$ i.i.d. bounded real random variables $h(x,\omega^j)$ with expectation $f(x)$, so both tails are one-dimensional large deviations. Applied at each of the finitely many points $x_1,\dots,x_q$ of Lemma 2.4 (c), it turns the union bound of p. 13 into the rate of Theorem 3.2.
--
--   **Formalization Note** "$\exists\beta>0$ with $\limsup_N N^{-1}\log Q(\cdot)\le-\beta$" is stated in the equivalent form: for every $\delta>0$, eventually $Q(\cdot)\le e^{-(\beta-\delta)N}$. This avoids the logarithm of a probability that may be $0$. Hypotheses (ii)–(iv) of Theorem 2.3 play no role in this step and are not assumed.
-- source:
--   Shapiro & Homem-de-Mello, On Rate of Convergence of Optimal Solutions of Monte Carlo Approximations of Stochastic Programs, preprint (SPEPS copy, edoc.hu-berlin.de), p. 13, proof of Theorem 3.2, the two lim sup displays

import Mathlib
import Definitions.Def_SAARate_Polyhedral_Setting

open MeasureTheory ProbabilityTheory Filter

namespace SAARate.Polyhedral

/-- Proof of Theorem 3.2, p. 13: for a finite scenario space, a fixed point `x` and `ε > 0`,
both tails `P(f̂_N(x) ≥ f(x) + ε)` and `P(f̂_N(x) ≤ f(x) − ε)` decay exponentially:
there is `β > 0` with `limsup_N N⁻¹ log P(·) ≤ −β`, stated in ε-form
(`∀ δ > 0`, eventually `P(·) ≤ exp(−(β − δ) N)`). -/
theorem pointwise_exponential_bounds {m : ℕ} {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : SAARate.Sharp.E m → Ω → ℝ)
    {S : Type*} [MeasurableSpace S] (Q : Measure S) [IsProbabilityMeasure Q]
    (ω : ℕ → S → Ω) (hω : SAARate.SharpLD.IsIIDSample Q P ω) (x : SAARate.Sharp.E m) (ε : ℝ) (hε : 0 < ε) :
    (∃ β > 0, ∀ δ > 0, ∀ᶠ N : ℕ in atTop,
        Q {s | SAARate.Sharp.expectedObj P h x + ε ≤ SAARate.Sharp.saaObj h (fun j => ω j s) N x} ≤
          ENNReal.ofReal (Real.exp (-(β - δ) * (N : ℝ)))) ∧
      (∃ β > 0, ∀ δ > 0, ∀ᶠ N : ℕ in atTop,
        Q {s | SAARate.Sharp.saaObj h (fun j => ω j s) N x ≤ SAARate.Sharp.expectedObj P h x - ε} ≤
          ENNReal.ofReal (Real.exp (-(β - δ) * (N : ℝ)))) := by sorry

end SAARate.Polyhedral
