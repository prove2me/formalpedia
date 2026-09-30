-- Prove2me | Theorems.Thm_SabanisEuler_Rate_taming_error
-- name    : SabanisEuler.Rate.taming_error
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T23:11:14.838741+00:00
-- url     : https://prove2.me/theorems/632ee6b7-db2a-4620-90ca-59c5afb0a7ea
-- title:
--   Lemma 3 — the taming error is of order $n^{-\alpha p}$
-- statement:
--   Let $b_n,\sigma_n$ be the tamed coefficients (2.11)–(2.12) with some $\alpha\in(0,1/2]$ and the exponent $l>0$ of A-6, and for every $n\ge1$ let $X_n$ solve the scheme (2.2) with these coefficients on $[0,T]$. Suppose A-2 and A-4–A-6 hold, and let $0<p\le\frac{p_0}{2l+1}$. Then there is a constant $C$, independent of $n$, such that for every $n\ge1$
--   $$\mathbb E\Big[\int_0^T|b(s,X_n(\kappa_n(s)))-b_n(s,X_n(\kappa_n(s)))|^p\,ds\Big]\le Cn^{-\alpha p}$$
--   and
--   $$\mathbb E\Big[\int_0^T|\sigma(s,X_n(\kappa_n(s)))-\sigma_n(s,X_n(\kappa_n(s)))|^p\,ds\Big]\le Cn^{-\alpha p}.$$
--
--   The lemma quantifies the price of taming: the tamed coefficients, evaluated along the scheme, differ from the true coefficients by $O(n^{-\alpha})$ in $L^p(ds\otimes dP)$. With $\alpha=1/2$ this is exactly the order of the main theorem.
--
--   **Formalization Note** The expectation of the time integral is an iterated lower Lebesgue integral in $[0,\infty]$; the integrand is jointly measurable because $\kappa_n$ takes countably many values. One constant serves both bounds, as printed.
-- source:
--   Sabanis, Euler approximations with varying coefficients, arXiv:1308.1796v4, p. 15, Lemma 3, eqs. (4.1)–(4.2)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_SabanisEuler_Shared_Conditions
import Definitions.Def_SabanisEuler_Shared_Model2

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open SabanisEuler.Shared

namespace SabanisEuler.Rate

open EthierKurtz

/-- Sabanis (2016), arXiv:1308.1796v4, p. 15, Lemma 3, eqs. (4.1)–(4.2): for the scheme (2.2)
with the tamed coefficients (2.11)–(2.12) of Model 2 (exponent `α ∈ (0, 1/2]`), under A-2,
A-4–A-6 and `0 < p ≤ p₀ / (2l + 1)`, there is a constant `C` independent of `n` with
`𝔼 ∫₀ᵀ |b(s, Xₙ(κₙ(s))) - bₙ(s, Xₙ(κₙ(s)))|^p ds ≤ C n^{-αp}` and
`𝔼 ∫₀ᵀ |σ(s, Xₙ(κₙ(s))) - σₙ(s, Xₙ(κₙ(s)))|^p ds ≤ C n^{-αp}` for every `n ≥ 1`.
One constant serves both bounds, as printed. -/
theorem taming_error
    {d d₁ : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 mΩ) [ℱ.IsRightContinuous]
    (W : ℝ≥0 → Ω → SDEState d₁) (hW : IsWienerMartingale P ℱ W)
    (T : ℝ≥0) (hT : 0 < T)
    (p₀ p₁ : ℝ) (hp₀ : 2 ≤ p₀) (hp₁ : 2 ≤ p₁)
    (b : ℝ≥0 × SDEState d → SDEState d) (σ : ℝ≥0 × SDEState d → Diffusion d d₁)
    (hb : Measurable b) (hσ : Measurable σ)
    (ξ : Ω → SDEState d) (hξ : Measurable[ℱ 0] ξ)
    (l : ℝ)
    (hA2 : CondA2 T b) (hA4 : CondA4 T p₀ b σ) (hA5 : CondA5 P p₀ ξ)
    (hA6 : CondA6 T p₁ l b σ)
    (α : ℝ) (hα : 0 < α ∧ α ≤ 1 / 2)
    (p : ℝ) (hp : 0 < p) (hpl : p ≤ p₀ / (2 * l + 1))
    (Xₙ : ℕ → ℝ≥0 → Ω → SDEState d)
    (hXₙ : ∀ n : ℕ, 1 ≤ n →
      IsSchemeSolution P ℱ W T ξ (tamedDrift α l b) (tamedDiffusion α l σ) n (Xₙ n)) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      (∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) (T : ℝ),
          ‖b (s.toNNReal, Xₙ n (kappa n s.toNNReal) ω)
            - tamedDrift α l b n (s.toNNReal, Xₙ n (kappa n s.toNNReal) ω)‖ₑ ^ p) ∂P)
        ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-(α * p))) ∧
      (∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) (T : ℝ),
          ‖σ (s.toNNReal, Xₙ n (kappa n s.toNNReal) ω)
            - tamedDiffusion α l σ n (s.toNNReal, Xₙ n (kappa n s.toNNReal) ω)‖ₑ ^ p) ∂P)
        ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-(α * p))) := by sorry

end SabanisEuler.Rate
