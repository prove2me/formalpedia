-- Prove2me | Theorems.Thm_PrefDeals_lemma_6
-- name    : PrefDeals.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:18:00.980449+00:00
-- url     : https://prove2.me/theorems/993e7301-eb61-4b79-a9c3-128b191ce062
-- title:
--   Lemma 6 — first-order stochastic dominance: $F\ge G$ and $\varphi$ nondecreasing give $\int\varphi\,dF\le\int\varphi\,dG$
-- statement:
--   Let $\mu_F$ and $\mu_G$ be probability distributions on $\mathbb R$ with distribution functions $F$ and $G$ satisfying
--
--   $$
--   F(x)\ \ge\ G(x)\qquad\text{for all }x\in\mathbb R,
--   $$
--
--   and let $\varphi:\mathbb R\to\mathbb R$ be nondecreasing and integrable with respect to both. Then
--
--   $$
--   \int\varphi\,d\mu_F\ \le\ \int\varphi\,d\mu_G .
--   $$
--
--   When $F$ and $G$ have densities $f$ and $g$, this is $\int\varphi(x)f(x)\,dx\le\int\varphi(x)g(x)\,dx$. The paper uses it to compare conditional laws of the common value component (Lemma 7) and of a buyer's valuation (Lemma 5).
--
--   Differences from the source:
--   - generalization: probability distributions $F$, $G$ with p.d.f.'s $f$, $g$ → arbitrary probability measures on $\mathbb R$ with distribution functions $F\ge G$; reason: distributions with densities are a special case; with densities the integrals agree
--   - encoding: $\int_{-\infty}^{\infty}\varphi(x)f(x)dx$ and $\int_{-\infty}^{\infty}\varphi(x)g(x)dx$ taken for granted → $\varphi$ integrable with respect to both distributions; reason: only excludes undefined integrals (Lean's Bochner integral is $0$ there)
-- source:
--   Kim, Mirrokni & Nazerzadeh, Deals or No Deals: Contract Design for Online Advertising, SSRN 2693037, Lemma 6, p.27

import Mathlib

open MeasureTheory ProbabilityTheory

namespace PrefDeals

/-- **Lemma 6: first-order stochastic dominance and nondecreasing functions.**
Kim, Mirrokni & Nazerzadeh, *Deals or No Deals*, SSRN 2693037, Lemma 6, p.27: "Let `φ : ℝ → ℝ` be a
non-decreasing function. Let `F` and `G` be two probability distributions, with p.d.f.'s `f` and
`g`, satisfying `F(x) ≥ G(x)` for all `x ∈ ℝ`. Then, `∫_{−∞}^{∞} φ(x)f(x)dx ≤ ∫_{−∞}^{∞} φ(x)g(x)dx`."

Let `μ_F` and `μ_G` be probability measures on `ℝ` whose distribution functions satisfy
`F(x) ≥ G(x)` for all `x`, and let `φ` be nondecreasing and integrable for both. Then
`∫ φ dμ_F ≤ ∫ φ dμ_G`.

**Formalization Note.** The distributions need not have densities (with densities `f`, `g`,
`∫ φ dμ_F = ∫ φ(x) f(x) dx`). Integrability of `φ` makes both integrals finite, which the paper
takes for granted. -/
theorem lemma_6 (φ : ℝ → ℝ) (hφ : Monotone φ) (μF μG : Measure ℝ)
    [IsProbabilityMeasure μF] [IsProbabilityMeasure μG]
    (hFG : ∀ x, cdf μG x ≤ cdf μF x)
    (hiF : Integrable φ μF) (hiG : Integrable φ μG) :
    ∫ x, φ x ∂μF ≤ ∫ x, φ x ∂μG := by sorry

end PrefDeals
