-- Prove2me | Theorems.Thm_SmoothedSimplex_Shadow_almost_polynomial_densities
-- name    : SmoothedSimplex.Shadow.almost_polynomial_densities
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:47:39.848555+00:00
-- url     : https://prove2.me/theorems/6b955179-a741-482a-a374-b5363b6c8376
-- title:
--   Lemma 2.3.7 — almost polynomial densities: $\Pr[t<\varepsilon]\le c(\varepsilon/t_0)^{k+1}$
-- statement:
--   Let $k>0$ and let $t$ be a non-negative random variable with density proportional to $\mu(t)\,t^k$, where $\mu\ge0$ is measurable. Suppose that for some $t_0>0$ the function $\mu$ is positive on $[0,t_0]$ and
--
--   $$
--   \frac{\max_{0\le t\le t_0}\mu(t)}{\min_{0\le t\le t_0}\mu(t)}\le c .
--   $$
--
--   Then for every $\varepsilon$,
--
--   $$
--   \Pr[t<\varepsilon]\le c\,(\varepsilon/t_0)^{k+1}.
--   $$
--
--   Near the origin such a density behaves like $t^k$ up to the factor $c$, so small values of $t$ are polynomially unlikely; the lemma is used for the heights in Lemma 4.1.3 and the angle in Lemma 4.2.2.
--
--   **Formalization Note** The page states the strict inequality $<$, but its proof gives $\le$, and $<$ fails (for $\mu=1$ on $[0,t_0]$ and $0$ beyond, $c=1$ and $\varepsilon=t_0$ give $1=1$); this item states $\le$. "Density proportional to $\mu(t)t^k$" is cross-multiplied: $\int_{[0,\varepsilon)}\mu(t)t^k\,dt\le c(\varepsilon/t_0)^{k+1}\int_{[0,\infty)}\mu(t)t^k\,dt$. The ratio condition is written as $\mu(t)\le c\,\mu(t')$ for all $t,t'\in[0,t_0]$.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Lemma 2.3.7, printed p. 18 (PDF p. 18); proof p. 19

import Mathlib

namespace SmoothedSimplex.Shadow

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

/-- **Lemma 2.3.7 (Almost polynomial densities)** (Spielman & Teng, arXiv:cs/0111050v7,
Lemma 2.3.7, printed p. 18, PDF p. 18). Let `k > 0` and let `t` be a non-negative random variable
with density proportional to `µ(t) t^k` such that, for some `t₀ > 0`,
`max_{0≤t≤t₀} µ(t) / min_{0≤t≤t₀} µ(t) ≤ c`. Then `Pr[t < ε] ≤ c (ε/t₀)^{k+1}`.

**Formalization Note.**
* **Corrected inequality.** The page states the strict `Pr[t < ε] < c(ε/t₀)^{k+1}`, but its proof
  (p. 19) gives `≤`, and `<` fails: for `µ = 1` on `[0, t₀]` and `µ = 0` beyond, `c = 1`,
  `ε = t₀`, both sides equal `1`. This item states `≤`.
* "Density proportional to `µ(t)t^k`" is cross-multiplied: `∫_{[0,ε)} µ(t)t^k dt ≤
  c(ε/t₀)^{k+1} ∫_{[0,∞)} µ(t)t^k dt`, with lower Lebesgue integrals (no `0/0`).
* `µ` is a measurable non-negative function. The ratio `max/min ≤ c` is read as: `µ > 0` on
  `[0, t₀]` (so the ratio is defined) and `µ(t) ≤ c µ(t')` for all `t, t' ∈ [0, t₀]`.
* `k` is real; `t^k` and `(ε/t₀)^{k+1}` are real powers. -/
theorem almost_polynomial_densities (μ : ℝ → ℝ) (hμm : Measurable μ) (hμ0 : ∀ t, 0 ≤ μ t)
    (k : ℝ) (hk : 0 < k) (t₀ c : ℝ) (ht₀ : 0 < t₀)
    (hpos : ∀ t ∈ Set.Icc 0 t₀, 0 < μ t)
    (hc : ∀ t ∈ Set.Icc 0 t₀, ∀ t' ∈ Set.Icc 0 t₀, μ t ≤ c * μ t') (ε : ℝ) :
    ∫⁻ t in Set.Ico 0 ε, ENNReal.ofReal (μ t * t ^ k) ≤
      ENNReal.ofReal (c * (ε / t₀) ^ (k + 1)) *
        ∫⁻ t in Set.Ici 0, ENNReal.ofReal (μ t * t ^ k) := by sorry

end SmoothedSimplex.Shadow
