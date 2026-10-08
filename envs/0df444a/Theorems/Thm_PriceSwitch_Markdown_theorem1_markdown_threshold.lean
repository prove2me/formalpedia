-- Prove2me | Theorems.Thm_PriceSwitch_Markdown_theorem1_markdown_threshold
-- name    : PriceSwitch.Markdown.theorem1_markdown_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:08:19.388975+00:00
-- url     : https://prove2.me/theorems/872a3835-fe1a-453a-806f-1b2d9b51f86f
-- title:
--   Theorem 1 — optimal markdown at increasing inventory thresholds
-- statement:
--   Start with $n$ units at price $p_1$ and allow one switch to a lower price $p_2$. Demand at the two prices has positive Poisson rates $\lambda_1<\lambda_2$, and the revenue rates satisfy $p_1\lambda_1<p_2\lambda_2$. The salvage value is zero. Let $J(n,t;0)$ be the revenue from switching immediately, $J(n,t)$ the optimal stopping value, and $G$ the function defined from the immediate-switch Poisson tail.
--
--   There exist strictly increasing time-to-go thresholds $x_1<x_2<\cdots$ and functions $F,H$ with $F(0,t)=0$. For $n\ge1$, write $L(n,t)=G(n,t)+\lambda_1F(n-1,t)$. Then $H$ solves the differential equation and boundary condition
--
--   $$
--   \partial_t H(n,t)=-\lambda_1H(n,t)+L(n,t)\quad(t>0),\qquad H(n,x_n)=0,
--   $$
--
--   while $x_n=\inf\{t\ge0:L(n,t)=0\}$ with a nonempty defining set, and $F(n,t)=0$ for $t<x_n$ and $F(n,t)=H(n,t)$ for $t\ge x_n$. The optimal value is
--
--   $$
--   J(n,t)=\begin{cases}J(n,t;0),&t\le x_n,\\J(n,t;0)+F(n,t),&t>x_n.\end{cases}
--   $$
--
--   If $y_n=\inf\{s\ge0:G(n,s)=0\}$, then $x_1=y_1$ and $x_n<y_n$ for $n>1$. This gives the stock-dependent timing rule and the full value representation of Theorem 1.
--
--   **Formalization Note** The thresholds and functions are constructed existentially and fixed by the recursion, zero sets, ODE and boundary values; equality with $J$ is a conclusion. The first demand process is the referenced Poisson counting process with exponential interarrivals. The combined demand in $J(n,t;s)$ uses its Poisson law. Time-to-go is nonnegative, thresholds are indexed from one, and nonempty zero sets make the real infima meaningful. The paper's positive prices and rates are explicit in the markdown hypothesis; the probability-measure instance is redundant with the interarrival law. Stopping payoffs are bounded and measurable.
-- source:
--   Feng & Gallego (1995), Management Science 41(8), Theorem 1, p. 1380, https://doi.org/10.1287/mnsc.41.8.1371

import Mathlib
import Definitions.Def_PriceSwitch_Markdown_Model

namespace PriceSwitch.Markdown

open MeasureTheory QueueingFundamentals.Foundations

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Feng–Gallego (1995), Theorem 1, p. 1380: the markdown value and its increasing thresholds. -/
theorem theorem1_markdown_threshold
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ → Ω → ℝ)
    (p₁ lam₁ p₂ lam₂ : ℝ) (hpair : IsMarkdownPair p₁ lam₁ p₂ lam₂)
    (hT : IsExpInterarrivals P lam₁ T) :
    ∃ (x : ℕ → ℝ) (F H : ℕ → ℝ → ℝ),
      StrictMonoOn x (Set.Ici 1) ∧
      (∀ t, F 0 t = 0) ∧
      (∀ n, 1 ≤ n →
        (∀ t, 0 < t → HasDerivAt (H n)
          (-lam₁ * H n t + G p₁ lam₁ p₂ lam₂ n t + lam₁ * F (n - 1) t) t) ∧
        H n (x n) = 0 ∧
        (∃ t, 0 ≤ t ∧ G p₁ lam₁ p₂ lam₂ n t + lam₁ * F (n - 1) t = 0) ∧
        x n = sInf {t : ℝ | 0 ≤ t ∧
          G p₁ lam₁ p₂ lam₂ n t + lam₁ * F (n - 1) t = 0} ∧
        (∀ t, F n t = if t < x n then 0 else H n t)) ∧
      x 1 = sInf {s : ℝ | 0 ≤ s ∧ G p₁ lam₁ p₂ lam₂ 1 s = 0} ∧
      (∀ n, 1 < n → x n < sInf {s : ℝ | 0 ≤ s ∧ G p₁ lam₁ p₂ lam₂ n s = 0}) ∧
      (∀ n, 1 ≤ n → ∀ t, 0 ≤ t →
        optRevenue P T p₁ lam₁ p₂ lam₂ n t =
          if t ≤ x n then switchRevenue p₁ lam₁ p₂ lam₂ n t 0
          else switchRevenue p₁ lam₁ p₂ lam₂ n t 0 + F n t) := by sorry

end PriceSwitch.Markdown
