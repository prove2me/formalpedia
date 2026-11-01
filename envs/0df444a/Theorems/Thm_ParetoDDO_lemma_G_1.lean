-- Prove2me | Theorems.Thm_ParetoDDO_lemma_G_1
-- name    : ParetoDDO.lemma_G_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:34:16.940318+00:00
-- url     : https://prove2.me/theorems/cc70a381-3b7e-4664-981e-c30ea2125813
-- title:
--   Lemma G.1 — convergence in probability with an integrable dominator gives convergence of expectations
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and $z_T$, $T\in\mathbb N$, real random variables that converge in probability to a random variable $z_\infty$. If a random variable $\bar z$ with $\mathbb E[\bar z]<\infty$ satisfies $|z_T|\le\bar z$ for all $T$, then
--   $$
--   \lim_{T\to\infty}\mathbb E[z_T]=\mathbb E[z_\infty].
--   $$
--
--   This identifies the asymptotic in-sample risk $\lim_T\mathbb E_\theta[\widehat c_T(\widehat x_T)]$ of every data-driven pair.
--
--   **Formalization Note** Random variables are measurable functions; $\mathbb E[\bar z]<\infty$ is integrability of $\bar z$.
--
--   Differences from the source:
--   - encoding: time $T\in\mathbb N=\{1,2,\dots\}$ → `T : ℕ` with every condition imposed for $1\le T$; the $T=0$ slice is unconstrained; reason: Lean's ℕ contains 0; limits ignore one term, so the objects are the same
--   - encoding: random variables $z_T$, $z_\infty$, $\bar z$ with $\mathbb E[\bar z]<\infty$ → measurable functions, with $\bar z$ integrable; reason: the meaning of the words; $\bar z\ge|z_T|\ge0$ a.s., so finiteness of $\mathbb E[\bar z]$ is integrability
--   - generalization: $|z_T|\le\bar z$ (everywhere) → $|z_T|\le\bar z$ almost surely; reason: an everywhere bound is an almost-sure bound, so the source's statement is a special case; Definition 2.2(iii) supplies only an a.s. bound
-- source:
--   Sutter, Van Parys, Kuhn, A Pareto dominance principle for data-driven optimization, arXiv:2010.06606v4, Lemma G.1, p.50

import Mathlib
import Definitions.Def_ParetoDDO_Setting

open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace ParetoDDO

/-- **Lemma G.1** (Sutter, Van Parys, Kuhn, arXiv:2010.06606v4, p.50). On a probability space, if real random
variables `z_T`, `T ∈ ℕ`, converge in probability to a random variable `z∞` and some random variable
`z̄` with `E[z̄] < ∞` satisfies `|z_T| ≤ z̄` for all `T`, then `lim_T E[z_T] = E[z∞]`.

**Formalization Note** Time is `T ∈ {1, 2, …}`; the `T = 0` term is unconstrained. The bound
`|z_T| ≤ z̄` is required almost surely. -/
theorem lemma_G_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (z : ℕ → Ω → ℝ) (zinf zbar : Ω → ℝ)
    (hz : ∀ T, 1 ≤ T → Measurable (z T)) (hzinf : Measurable zinf) (hzbar : Measurable zbar)
    (hconv : TendstoInMeasure μ z atTop zinf)
    (hdom : ∀ T, 1 ≤ T → ∀ᵐ ω ∂μ, |z T ω| ≤ zbar ω) (hint : Integrable zbar μ) :
    Tendsto (fun T => ∫ ω, z T ω ∂μ) atTop (𝓝 (∫ ω, zinf ω ∂μ)) := by sorry

end ParetoDDO
