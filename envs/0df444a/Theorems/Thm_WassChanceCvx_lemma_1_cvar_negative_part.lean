-- Prove2me | Theorems.Thm_WassChanceCvx_lemma_1_cvar_negative_part
-- name    : WassChanceCvx.lemma_1_cvar_negative_part
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:25:56.960966+00:00
-- url     : https://prove2.me/theorems/82493455-8d2d-4d8a-a4b6-6ecb8d6506b6
-- title:
--   Lemma 1 — $\mathrm{CVaR}_{1-\epsilon}(X^-)$ in terms of $\mathrm{CVaR}_{1-\epsilon}(X)$
-- statement:
--   Let $X$ be a real random variable on a probability space with $\mathbb E[X^+]<\infty$, and let $\epsilon\in(0,1)$. Write $(a)^+=\max\{a,0\}$ and $(a)^-=\min\{a,0\}$. Then
--
--   $$
--   \mathrm{CVaR}_{1-\epsilon}(X^-)=\mathbb 1\{0\ge\mathrm{VaR}_{1-\epsilon}(X)\}\cdot\Bigl[\mathrm{CVaR}_{1-\epsilon}(X)-\frac1\epsilon\mathbb E[X^+]\Bigr].
--   $$
--
--   Applied to $X=-f(x,\zeta)$, it relates the CVaR of $-d(\zeta,\mathcal S^c(x))=(-f(x,\zeta))^-$ in Proposition 1 to the CVaR of the slack, which gives Corollary 1.
--
--   **Formalization Note** $X$ is a measurable function on a probability space; VaR and CVaR are those of its law. Here $X^-=\min\{X,0\}\le0$, the paper's notation, not the usual nonnegative negative part.
--
--   Differences from the source:
--   - encoding: a random variable $X$ → a measurable `X : Ω → ℝ` on a probability space; VaR and CVaR of its law `μ.map X`; reason: VaR and CVaR depend only on the law
--   - encoding: no integrability hypothesis → $\mathbb E[X^+]<\infty$ (`Integrable (fun ω => max (X ω) 0) μ`); reason: otherwise the right side is $\infty-\infty$ and the identity is undefined
--   - encoding: $1-\epsilon\in(0,1)$, the standing assumption of p.1 → hypotheses `0 < ϵ` and `ϵ < 1`; reason: same range
--   - encoding: $\min_\gamma$ in Definition 5 → the real infimum `⨅ γ`; reason: the objective is bounded below and attains its minimum when $\mathbb E[X^+]<\infty$ and $\epsilon\in(0,1)$
-- source:
--   Shen, Jiang, Convex Chance-Constrained Programs with Wasserstein Ambiguity, arXiv:2111.02486v2, Lemma 1, p.7 (notation p.4)

import Mathlib
import Definitions.Def_WassChanceCvx_VaR
import Definitions.Def_WassChanceCvx_CVaR

open MeasureTheory

namespace WassChanceCvx

/-- **Lemma 1 (CVaR of the negative part).**
Shen, Jiang, arXiv:2111.02486v2, Lemma 1, p.7: "Let `X` be a random variable, then
`CVaR_{1−ϵ}(X⁻) = 𝟙{0 ≥ VaR_{1−ϵ}(X)} · [CVaR_{1−ϵ}(X) − (1/ϵ)𝔼[X⁺]]`", with the notation of p.4,
`(a)⁺ := max{a, 0}` and `(a)⁻ := min{a, 0}`.

**Formalization Note.** `X` is a measurable real function on a probability space `(Ω, μ)`; VaR and
CVaR are taken of its law `μ.map X`, and `X⁻ = min{X, 0}` (not the usual nonnegative negative
part). `𝔼[X⁺] < ∞` is assumed: otherwise the right side is `∞ − ∞`. `ϵ ∈ (0, 1)` is the standing
assumption of p.1. -/
theorem lemma_1_cvar_negative_part {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (hXpos : Integrable (fun ω => max (X ω) 0) μ) (ϵ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1) :
    CVaR (1 - ϵ) (μ.map (fun ω => min (X ω) 0)) =
      (if 0 ≥ VaR (1 - ϵ) (μ.map X) then (1 : ℝ) else 0) *
        (CVaR (1 - ϵ) (μ.map X) - (1 / ϵ) * ∫ ω, max (X ω) 0 ∂μ) := by sorry

end WassChanceCvx
