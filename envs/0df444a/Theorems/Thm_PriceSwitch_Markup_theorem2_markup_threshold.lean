-- Prove2me | Theorems.Thm_PriceSwitch_Markup_theorem2_markup_threshold
-- name    : PriceSwitch.Markup.theorem2_markup_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:01:43.733824+00:00
-- url     : https://prove2.me/theorems/8cfa1755-be4d-4050-9bfb-cf3f7d1e1e92
-- title:
--   Theorem 2 — optimal markup at an increasing time-to-go threshold
-- statement:
--   Start with $n\ge1$ items and charge price $p_1$ until an adaptive switch to $p_2>p_1$, with Poisson rates $\lambda_1>\lambda_2>0$ and revenue rates $p_1\lambda_1>p_2\lambda_2$. Let $J(n,t)$ be the optimal expected revenue over admissible switch times, and $J(n,t;0)$ the revenue from switching immediately. There are nondecreasing thresholds $(z_n)_{n\ge1}$, auxiliary thresholds $x_n$, and functions $F,H$ such that
--
--   $$
--   y_n\le x_n<z_n,\qquad
--   J(n,t)=\begin{cases}J(n,t;0)+F(n,t),&t<z_n,\\J(n,t;0),&t\ge z_n,\end{cases}
--   $$
--
--   where $y_n$ is the first nonnegative zero of $G(n,\cdot)$, $F(0,t)=0$, and $F(n,t)=H(n,t)$ below $z_n$ and $0$ at or above it. For $n\ge1$, $H(n,0)=0$ and
--
--   $$
--   \partial_tH(n,t)=-\lambda_1H(n,t)+L(n,t),\quad L(n,t)=G(n,t)+\lambda_1F(n-1,t),\quad
--   x_n=\inf\{t\ge0:L(n,t)=0\},\quad z_n=\inf\{t>0:H(n,t)=0\}.
--   $$
--
--   These thresholds specify when an immediate price increase is optimal and how the continuation value varies with inventory and time-to-go.
--
--   **Formalization Note** The stopping value uses the independent Poisson count sum through its Poisson law. The zero sets defining $y_n$, $x_n$, and $z_n$ are asserted nonempty to prevent a default infimum; the positive-zero condition for $z_n$ is retained. Continuity of $H(n,\cdot)$ at zero connects its boundary value to the ODE. The probability-measure assumption is explicit but follows from the exponential interarrival law. The theorem itself assumes no verification equation, sign-change conclusion, or revenue identity.
-- source:
--   Feng & Gallego (1995), Management Science 41(8), §4.3, Theorem 2, pp. 1382–1383, https://doi.org/10.1287/mnsc.41.8.1371

import Mathlib
import Definitions.Def_PriceSwitch_Markdown_Model

namespace PriceSwitch.Markup

open MeasureTheory QueueingFundamentals.Foundations

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Feng–Gallego (1995), Theorem 2, pp. 1382–1383. -/
theorem theorem2_markup_threshold
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ → Ω → ℝ)
    (p₁ lam₁ p₂ lam₂ : ℝ) (hpair : PriceSwitch.Markdown.IsMarkupPair p₁ lam₁ p₂ lam₂)
    (hT : IsExpInterarrivals P lam₁ T) :
    ∃ (x z : ℕ → ℝ) (F H : ℕ → ℝ → ℝ),
      MonotoneOn z (Set.Ici 1) ∧
      (∀ n, 1 ≤ n →
        (∃ s, 0 ≤ s ∧ PriceSwitch.Markdown.G p₁ lam₁ p₂ lam₂ n s = 0) ∧
        sInf {s : ℝ | 0 ≤ s ∧ PriceSwitch.Markdown.G p₁ lam₁ p₂ lam₂ n s = 0} ≤ x n ∧ x n < z n) ∧
      (∀ t, 0 ≤ t → F 0 t = 0) ∧
      (∀ n, 1 ≤ n →
        H n 0 = 0 ∧
        ContinuousWithinAt (H n) (Set.Ici 0) 0 ∧
        (∀ t, 0 < t → HasDerivAt (H n)
          (-lam₁ * H n t + (PriceSwitch.Markdown.G p₁ lam₁ p₂ lam₂ n t + lam₁ * F (n - 1) t)) t) ∧
        (∃ t, 0 ≤ t ∧ PriceSwitch.Markdown.G p₁ lam₁ p₂ lam₂ n t + lam₁ * F (n - 1) t = 0) ∧
        x n = sInf {t : ℝ | 0 ≤ t ∧
          PriceSwitch.Markdown.G p₁ lam₁ p₂ lam₂ n t + lam₁ * F (n - 1) t = 0} ∧
        (∃ t, 0 < t ∧ H n t = 0) ∧
        z n = sInf {t : ℝ | 0 < t ∧ H n t = 0} ∧
        (∀ t, 0 ≤ t → F n t = if t < z n then H n t else 0)) ∧
      (∀ n, 1 ≤ n → ∀ t, 0 ≤ t →
        PriceSwitch.Markdown.optRevenue P T p₁ lam₁ p₂ lam₂ n t =
          if t < z n then PriceSwitch.Markdown.switchRevenue p₁ lam₁ p₂ lam₂ n t 0 + F n t
          else PriceSwitch.Markdown.switchRevenue p₁ lam₁ p₂ lam₂ n t 0) := by sorry

end PriceSwitch.Markup
