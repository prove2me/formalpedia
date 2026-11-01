-- Prove2me | Theorems.Thm_WassChanceCvx_proposition_8_borell_brascamp_lieb
-- name    : WassChanceCvx.proposition_8_borell_brascamp_lieb
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:25:45.579517+00:00
-- url     : https://prove2.me/theorems/f6bf2467-c2ab-4237-905f-8bf5d57430ed
-- title:
--   Proposition 8 (corrected: weights $\theta,1-\theta$ on $x_0,x_1$) — Borell–Brascamp–Lieb inequality
-- statement:
--   Let $n\ge1$, and let $f_0,f_1:\mathbb R^n\to[0,\infty)$ be Borel measurable and Lebesgue integrable with nonempty supports $S_0=\{f_0>0\}$ and $S_1=\{f_1>0\}$. Let $\theta\in(0,1)$, $\alpha\in[-1/n,+\infty]$, and let $f:\mathbb R^n\to[0,\infty)$ be measurable with
--
--   $$
--   f\bigl(\theta x_0+(1-\theta)x_1\bigr)\ \ge\ m_\alpha\bigl(f_0(x_0),f_1(x_1);\theta\bigr)\qquad\text{for all } x_0\in S_0,\ x_1\in S_1 .
--   $$
--
--   Then
--
--   $$
--   \int_{\theta S_0+(1-\theta)S_1}f(x)\,dx\ \ge\ m_{\alpha^*_n}\Bigl(\int_{S_0}f_0(x)\,dx,\ \int_{S_1}f_1(x)\,dx;\ \theta\Bigr),
--   $$
--
--   with $\alpha^*_n=\alpha/(1+n\alpha)$ for $\alpha>-1/n$, $1/n$ for $\alpha=+\infty$ and $-\infty$ for $\alpha=-1/n$.
--
--   Theorem 1's proof applies it with $n=1$, $\theta=\tfrac12$, in the variable $t$, to show that the right side of (5) is midpoint quasi-concave in $x$.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ` with Lebesgue measure. The left side is a lower Lebesgue integral in $[0,\infty]$ over the Minkowski combination, which is analytic and hence Lebesgue measurable; the right side is finite.
--
--   Differences from the source:
--   - correction: $x=(1-\theta)x_0+\theta x_1$ and the set $(1-\theta)S_0+\theta S_1$, with Definition 1's $m_\alpha(a,b;\theta)$ weighting the first argument by $\theta$ → $x=\theta x_0+(1-\theta)x_1$ and $\theta S_0+(1-\theta)S_1$; reason: as printed it is false: $n=1$, $\alpha=+\infty$, $\theta=0.9$, $f_0=\mathbb 1_{[0,10]}$, $f_1=\mathbb 1_{[0,1]}$, $f=\mathbb 1_{[0,1.9]}$ satisfy the hypothesis but $1.9\ge m_1(10,1;0.9)=9.1$ fails; the paper uses only $\theta=\tfrac12$, where both forms agree
--   - encoding: $-1/n\le\alpha$ (presupposes $n\ge1$) → hypothesis `1 ≤ n`; reason: $-1/n$ is undefined for $n=0$
--   - encoding: $f$ measurable → `AEMeasurable f` with respect to Lebesgue measure; reason: Lebesgue measurability, as in Gupta's theorem
--   - encoding: $\int_{(\cdot)}f(x)\,dx$ over the Minkowski combination; $\int_{S_i}f_i$ → lower Lebesgue integral `∫⁻` of `ofReal ∘ f` over the restricted measure; Bochner integrals over $S_i$; reason: $f\ge0$, so the lower integral is the integral (possibly $+\infty$); $f_0,f_1$ are integrable
--   - encoding: $\alpha\in\overline{\mathbb R}$ → `α : EReal`; reason: same values $[-\infty,+\infty]$
--   - reading: supports $S_0,S_1$ → the positivity sets $\{f_i>0\}$; reason: $m_\alpha$ vanishes when a factor is $0$, so the hypothesis is the same for the closed supports, and the positivity sets give the smaller integration set on the left, hence the stronger statement; the right side does not change
--   - encoding: Lebesgue measure on $\mathbb R^n$ → `volume` on `Fin n → ℝ`; reason: the same measure
-- source:
--   Shen, Jiang, Convex Chance-Constrained Programs with Wasserstein Ambiguity, arXiv:2111.02486v2, Proposition 8, p.31

import Mathlib
import Definitions.Def_KallMayerSLP_GenConcave_genMean
import Definitions.Def_WassChanceCvx_alphaStar

open MeasureTheory
open scoped Pointwise

namespace WassChanceCvx

/-- **Proposition 8 (Borell–Brascamp–Lieb inequality, after Gupta 1980), corrected.**
Shen, Jiang, arXiv:2111.02486v2, Proposition 8 (Theorem 2 in [Gup80]), p.31: "Let `f₀, f₁` be two
non-negative Borel-measurable functions on `ℝⁿ` with non-empty supports `S₀` and `S₁`,
respectively. Assume that `f₀` and `f₁` are integrable with respect to the Lebesgue measure on
`ℝⁿ`. Let `θ ∈ (0, 1)` be a fixed number and `f` be a non-negative, measurable function on `ℝⁿ`
such that `f(x) ≥ m_α[f₀(x₀), f₁(x₁); θ]`, whenever `x = (1 − θ)x₀ + θx₁` with `x₀ ∈ S₀, x₁ ∈ S₁;
−1/n ≤ α ≤ +∞`. Then `∫_{(1−θ)S₀+θS₁} f(x) dx ≥ m_{α*_n}[∫_{S₀} f₀(x) dx, ∫_{S₁} f₁(x) dx; θ]`."

**Correction.** With Definition 1's `m_α(a, b; θ) = (θa^α + (1 − θ)b^α)^{1/α}`, which puts the
weight `θ` on the first argument, the combination must be `x = θx₀ + (1 − θ)x₁` and the set
`θS₀ + (1 − θ)S₁`. As printed the statement is false: `n = 1`, `α = +∞`, `θ = 0.9`,
`f₀ = 𝟙_{[0,10]}`, `f₁ = 𝟙_{[0,1]}`, `f = 𝟙_{[0,1.9]}` satisfy the hypothesis, but
`1.9 ≥ m₁(10, 1; 0.9) = 9.1` fails. The paper applies it only at `θ = ½`, where both agree.

**Formalization Note.** `ℝⁿ = Fin n → ℝ` with Lebesgue measure `volume`; `n ≥ 1` (the range
`−1/n ≤ α` presupposes it). The supports are `Sᵢ = {fᵢ > 0}`. "Measurable" for `f` is read as
Lebesgue (almost-everywhere) measurability. The left side is a lower Lebesgue integral in
`[0, ∞]` over the Minkowski combination (an analytic, hence null-measurable, set); the right side
is real, the integrals of `f₀, f₁` being finite. `m_α(a, b; θ)` is the published
`KallMayerSLP.GenConcave.genMean α θ a b`. -/
theorem proposition_8_borell_brascamp_lieb {n : ℕ} (hn : 1 ≤ n)
    (f₀ f₁ f : (Fin n → ℝ) → ℝ)
    (hf₀m : Measurable f₀) (hf₁m : Measurable f₁)
    (hf₀ : ∀ x, 0 ≤ f₀ x) (hf₁ : ∀ x, 0 ≤ f₁ x)
    (hS₀ : {x | 0 < f₀ x}.Nonempty) (hS₁ : {x | 0 < f₁ x}.Nonempty)
    (hi₀ : Integrable f₀) (hi₁ : Integrable f₁)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hfm : AEMeasurable f) (hf : ∀ x, 0 ≤ f x)
    (α : EReal) (hα : ((-1 / (n : ℝ) : ℝ) : EReal) ≤ α)
    (hmean : ∀ x₀ ∈ {x | 0 < f₀ x}, ∀ x₁ ∈ {x | 0 < f₁ x},
      KallMayerSLP.GenConcave.genMean α θ (f₀ x₀) (f₁ x₁) ≤ f (θ • x₀ + (1 - θ) • x₁)) :
    ENNReal.ofReal (KallMayerSLP.GenConcave.genMean (alphaStar n α) θ (∫ x in {x | 0 < f₀ x}, f₀ x)
        (∫ x in {x | 0 < f₁ x}, f₁ x)) ≤
      ∫⁻ x in θ • {x | 0 < f₀ x} + (1 - θ) • {x | 0 < f₁ x}, ENNReal.ofReal (f x) := by sorry

end WassChanceCvx
