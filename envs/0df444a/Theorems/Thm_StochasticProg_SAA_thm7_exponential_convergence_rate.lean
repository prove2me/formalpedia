-- Prove2me | Theorems.Thm_StochasticProg_SAA_thm7_exponential_convergence_rate
-- name    : StochasticProg.SAA.thm7_exponential_convergence_rate
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T20:14:38.882975+00:00
-- url     : https://prove2.me/theorems/9577aeb9-c00e-4b87-99ad-5d3e6fb07f27
-- title:
--   Chapter 9, Theorem 7 — exponential-rate convergence of the SAA value and solution
-- statement:
--   **Chapter 9, Theorem 7** (Birge & Louveaux, p. 412; proof in Dai, Chen & Birge [2000],
--   Theorems 3.1–3.2): under a uniform exponential-moment condition, both the SAA optimal *value*
--   and (when the true optimum is unique) the SAA optimal *solution* converge to their true
--   counterparts with a probability of large deviation decaying exponentially in the sample size
--   $\nu$.
--
--   Fix a feasible set $X\subseteq\mathbb R^n$, an outcome space $\Xi$, and an integrand
--   $g:\mathbb R^n\times\Xi\to\mathbb R$. Let $\xi_1,\xi_2,\dots:\Omega\to\Xi$ be an i.i.d. sample
--   on a probability space $(\Omega,P)$ (independent, identically distributed as $\xi_1$). Let
--   $z^*$ be the optimal value of the true problem $\inf_{x\in X}\mathbb E\,g(x,\xi_1)$, attained
--   at $x^*\in X$, and, for each sample size $\nu$ and outcome $\omega$, let $z_\nu(\omega)$ be the
--   optimal value of the SAA problem $\min_{x\in X}\frac1\nu\sum_{i=1}^\nu g(x,\xi_i(\omega))$,
--   attained at $x_\nu(\omega)\in X$.
--
--   Assume there exist $a>0$, $\theta_0>0$ and $\eta:\Xi\to\mathbb R$ such that
--   $$
--   |g(x,\xi)|\le a\,\eta(\xi) \qquad (x\in X,\ \xi\in\Xi), \qquad
--   \mathbb E\bigl[e^{\theta\,\eta(\xi_1)}\bigr]<\infty \qquad (0\le\theta\le\theta_0).
--   $$
--   Then, for every $\varepsilon>0$, there exist $\alpha>0,\ \beta>0$ such that
--   $$
--   P\bigl[\,|z_\nu-z^*|\ge\varepsilon\,\bigr] \le \alpha\,e^{-\beta\nu} \qquad (\nu>0),
--   \tag{5.8}
--   $$
--   and, if $x^*$ is the **unique** optimal solution of the true problem,
--   $$
--   P\bigl[\,\|x_\nu-x^*\|\ge\varepsilon\,\bigr] \le \alpha\,e^{-\beta\nu} \qquad (\nu\ge1).
--   \tag{5.9}
--   $$
--
--   The book's own printed statement has a typo — an unmatched parenthesis, `P[E[zν − z*)] ≥ ε]`
--   — that this formalization corrects to the unambiguous `P[|zν − z*| ≥ ε]` its surrounding prose
--   plainly intends (the same quantity as (5.8) is discussed everywhere else in the section).
--
--   **Formalization Note** $\alpha$ and $\beta$ are existentially quantified exactly as the book
--   leaves them — the book proves their *existence*, citing Dai, Chen & Birge [2000] for the
--   argument, without supplying closed forms in terms of $a,\theta_0,\varepsilon$; sharpening them
--   to an explicit formula would be unfaithful (`reference/FAITHFULNESS_TRAPS.md`, trap 8: the
--   `∃ α, ∃ β` binders sit outside every other quantifier they must be uniform over, matching the
--   book's "for any $\varepsilon>0$, there are $\alpha,\beta$"). The integrand $g$ is left fully
--   abstract, as the book's §9.5 states it, rather than specialized to the two-stage recourse cost
--   $Q(x,\xi)$ of earlier chapters — this keeps the mission self-contained and matches the book's
--   own level of generality at this point in the text. $z^*$/$x^*$ and $z_\nu$/$x_\nu$ are given as
--   hypotheses characterizing them as optimal value and an optimal solution (a lower bound over $X$
--   plus attainment at the named point), not as `sInf`/`sSup` of an image set, to avoid the real
--   `sInf`/`sSup` junk-value trap on an unbounded or empty set (trap 5). The probability bound uses
--   `ENNReal.ofReal (α * Real.exp (-β * ν))` since `P` is `ℝ≥0∞`-valued in Mathlib; this coercion
--   is transparent whenever the bound is nonnegative, as it always is here since $\alpha,\beta>0$.
--   Because $g$ is abstract, the event's measurability is not automatic from the other hypotheses,
--   so `zSAA`/`xSAA` measurability is added explicitly (`hzSAA_meas`, `hxSAA_meas`) rather than
--   left implicit — the book is silent on this technical point, as is standard in an applied
--   convergence theorem, but Lean's `P {ω | …}` needs it to mean the actual probability rather than
--   an outer-measure value on a possibly non-measurable set. **Added 2026-09-19 (moderator
--   review):** `hgmeas : ∀ x ∈ X, Measurable (g x)`, mirroring Theorem 6's own hypothesis of the
--   same name. Without it, `g` could be chosen non-measurable in a way still consistent with
--   `hbound`'s pointwise bound, sending every occurrence of `∫ ω, g x (ξ 0 ω) ∂P` in `hxStar`,
--   `hzStar` and the uniqueness set to Mathlib's Bochner-integral junk value `0` — pinning `zStar`
--   to `0` and `xStar` to an arbitrary point of `X`, unrelated to the true problem's actual optimal
--   value/solution, while `zSAA`/`xSAA` (finite sums) kept computing correctly regardless. `hgmeas`
--   together with `hbound`/`hmgf` (which force `η` to have finite mean once `X` is nonempty) makes
--   `g x` genuinely integrable for every `x ∈ X`, closing this gap.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, p. 412, Chapter 9, Theorem 7 (eq. 5.8-5.9)

import Mathlib

namespace StochasticProg.SAA

open MeasureTheory ProbabilityTheory

variable {n : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]

/-- Chapter 9, Theorem 7 (Birge & Louveaux, p. 412): exponential-rate convergence of the sample
average approximation (SAA), both in value and (under uniqueness of the true optimum) in
solution. `X` is the deterministic feasible set of (5.1); `g` the (abstract) integrand;
`ξ : ℕ → Ω → Ξ` an i.i.d. sample sequence with common law; `zStar`/`xStar` the optimal value and
an optimal solution of (5.1); `zSAA ν ω`/`xSAA ν ω` the optimal value and an optimal solution of
the size-`ν` SAA problem (5.2) at sample outcome `ω`. The hypothesis bundle
`|g(x,ξ)| ≤ a·η(ξ)`, `E[e^{θη(ξ)}] < ∞` for `θ ∈ [0,θ0]` is the book's moment condition; the
conclusion gives, for every tolerance `ε`, constants `α,β` (existentially quantified, exactly as
the book leaves them abstract) with `P[|zSAA ν - zStar| ≥ ε] ≤ α·e^{-βν}` for every `ν > 0`
(eq. 5.8), and, if `xStar` is the unique optimal solution, `P[‖xSAA ν - xStar‖ ≥ ε] ≤ α·e^{-βν}`
for every `ν ≥ 1` (eq. 5.9).

**Formalization Note (fix, 2026-09-19, moderator review).** `hgmeas` requires `g x` measurable
for every `x ∈ X`, mirroring `thm6_saa_central_limit_theorem`'s own hypothesis. Without it,
`g` can be chosen so that `g x ∘ ξ 0` is not a.e. strongly measurable for every `x ∈ X` while
still satisfying `hbound`'s pointwise-everywhere bound (e.g. an indicator of a non-measurable
subset of `Ξ`); Mathlib's Bochner integral is then the junk value `0` on every occurrence of
`∫ ω, g x (ξ 0 ω) ∂P` above, which would pin `zStar` to `0` and let `xStar` be any point of `X`
— values unrelated to the genuine optimal value/solution of (5.1), while `zSAA`/`xSAA` (defined
via finite sums) keep computing the real sample averages regardless. `hgmeas`, together with
`hbound` and `hmgf` (which force `η` to have finite mean via Markov's inequality applied to
`e^{θ0 η}`, since `X` is nonempty via `xStar ∈ X`), makes `g x` genuinely integrable against
`P ∘ (ξ 0)⁻¹` for every `x ∈ X`, closing the gap rather than papering over it. -/
theorem thm7_exponential_convergence_rate
    (X : Set (EuclideanSpace ℝ (Fin n))) (g : EuclideanSpace ℝ (Fin n) → Ξ → ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P] (ξ : ℕ → Ω → Ξ)
    (hindep : iIndepFun ξ P) (hident : ∀ i, IdentDistrib (ξ i) (ξ 0) P P)
    (hgmeas : ∀ x ∈ X, Measurable (g x))
    (zStar : ℝ) (xStar : EuclideanSpace ℝ (Fin n))
    (hxStar : xStar ∈ X ∧ (∫ ω, g xStar (ξ 0 ω) ∂P) = zStar)
    (hzStar : ∀ x ∈ X, zStar ≤ ∫ ω, g x (ξ 0 ω) ∂P)
    (zSAA : ℕ → Ω → ℝ) (xSAA : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (hSAA : ∀ ν ω, xSAA ν ω ∈ X ∧
      (ν : ℝ)⁻¹ * ∑ i ∈ Finset.range ν, g (xSAA ν ω) (ξ i ω) = zSAA ν ω)
    (hSAA_opt : ∀ ν ω, ∀ x ∈ X, zSAA ν ω ≤ (ν : ℝ)⁻¹ * ∑ i ∈ Finset.range ν, g x (ξ i ω))
    (a θ0 : ℝ) (ha : 0 < a) (hθ0 : 0 < θ0) (η : Ξ → ℝ)
    (hbound : ∀ x ∈ X, ∀ ξ' : Ξ, |g x ξ'| ≤ a * η ξ')
    (hmgf : ∀ θ ∈ Set.Icc (0 : ℝ) θ0, Integrable (fun ω => Real.exp (θ * η (ξ 0 ω))) P)
    (hzSAA_meas : ∀ ν, Measurable (zSAA ν)) (hxSAA_meas : ∀ ν, Measurable (xSAA ν))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ α > 0, ∃ β > 0,
      (∀ ν > 0, P {ω | ε ≤ |zSAA ν ω - zStar|} ≤ ENNReal.ofReal (α * Real.exp (-β * ν))) ∧
      ((Set.Subsingleton {x ∈ X | (∫ ω, g x (ξ 0 ω) ∂P) = zStar}) →
        ∀ ν ≥ 1, P {ω | ε ≤ ‖xSAA ν ω - xStar‖} ≤ ENNReal.ofReal (α * Real.exp (-β * ν))) := by sorry

end StochasticProg.SAA
