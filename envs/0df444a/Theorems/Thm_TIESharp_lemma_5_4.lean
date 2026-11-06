-- Prove2me | Theorems.Thm_TIESharp_lemma_5_4
-- name    : TIESharp.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:36:20.225209+00:00
-- url     : https://prove2.me/theorems/a9e38953-8822-41c1-9d1d-342e863cb12a
-- title:
--   Lemma 5.4 — covariance bound for an expected maximum
-- statement:
--   Let $L_1,\dots,L_n$ be jointly distributed bounded loads and put $\mu_i=\mathbb E[L_i]$. Choose a maximizing machine $I$ and write $\theta_i=\Pr(I=i)$. Then
--   $$\mathbb E\big[\max_iL_i\big]\ \le\ \theta\cdot\mu+\sum_i\mathrm{width}(L_i)\,\theta_i(1-\theta_i),$$
--   where $\mathrm{width}(L)$ is the length of the smallest closed interval containing $L$ almost surely.
--
--   Differences from the source:
--   - generalization: width(L_i), the smallest interval containing L_i a.s. → any w_i with a_i ≤ L_i ≤ a_i + w_i a.s.; reason: the smallest interval is one such; the bound is monotone in w_i
--   - generalization: a maximizing machine chosen by a fixed tie-breaking rule → any measurable I with L_i ≤ L_I pointwise; reason: a fixed tie-breaking rule is such a selection
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), Lemma 5.4, p.25

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace TIESharp

/-- **Lemma 5.4 (Covariance bound for a maximum)** (Li, *Sharp Bounds for Truthful-in-Expectation
Scheduling*, arXiv:2611.05134, Lemma 5.4, p.25). Let `L_1, …, L_n` be jointly distributed bounded
loads and put `µ_i = E[L_i]`. Choose a maximizing machine `I` and write `θ_i = P(I = i)`. Then
`E[max_i L_i] ≤ θ · µ + Σ_i width(L_i) θ_i (1 − θ_i)`.

**Formalization Note.** The loads are measurable functions on a probability space `(Ω, P)`. Each
`L_i` lies almost surely in an interval `[a_i, a_i + w_i]`; the smallest such interval has length
`width(L_i)`, so the statement for every such interval contains the paper's. The maximizer `I` is
any measurable selection with `L_i ≤ L_I` pointwise; a fixed tie-breaking rule is one. -/
theorem lemma_5_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (L : Fin n → Ω → ℝ) (hL : ∀ i, Measurable (L i)) (I : Ω → Fin n)
    (hI : Measurable I) (hmax : ∀ ω i, L i ω ≤ L (I ω) ω) (a w : Fin n → ℝ)
    (hbd : ∀ i, ∀ᵐ ω ∂P, a i ≤ L i ω ∧ L i ω ≤ a i + w i) :
    ∫ ω, (⨆ i, L i ω) ∂P ≤
      ∑ i, (P (I ⁻¹' {i})).toReal * ∫ ω, L i ω ∂P
        + ∑ i, w i * (P (I ⁻¹' {i})).toReal * (1 - (P (I ⁻¹' {i})).toReal) := by sorry

end TIESharp
