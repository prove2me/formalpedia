-- Prove2me | Theorems.Thm_SAARate_Sharp_prop_2_2_eq_2_6
-- name    : SAARate.Sharp.prop_2_2_eq_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:05:44.613182+00:00
-- url     : https://prove2.me/theorems/6e97b6fe-2d93-4dca-aea7-5441ecec780d
-- title:
--   Proposition 2.2, (2.6), p. 5 — lim_N sup_{‖d‖≤1} |f′(x, d) − f̂′_N(x, d)| = 0 w.p.1
-- statement:
--   Let $P$ be a probability measure on $(\Omega,\mathcal F)$ and $h:\mathbb R^m\times\Omega\to\mathbb R$ with
--
--   1. $h(\cdot,\omega)$ convex for every $\omega\in\Omega$;
--   2. $f(x)=\mathbb E_P h(x,\omega)$ well defined and finite valued.
--
--   Let $\omega^1,\omega^2,\dots$ be an i.i.d. sample from $P$ and $\hat f_N(x)=N^{-1}\sum_{j=1}^N h(x,\omega^j)$. Then for every $x\in\mathbb R^m$,
--   $$
--   \lim_{N\to\infty}\ \sup_{\|d\|\le1}\ \bigl|f'(x,d)-\hat f'_N(x,d)\bigr| = 0\qquad\text{w.p.1}. \tag{2.6}
--   $$
--
--   So, w.p.1, the directional derivatives of the sample average function converge to those of the expected value function, uniformly over directions in the unit ball. In the proof of Theorem 2.1 this transfers the positive margin of $f'(\bar x,\cdot)$ on the unit sphere to $\hat f'_N(\bar x,\cdot)$.
--
--   **Formalization Note.** The limit of the supremum is stated as uniform convergence on the closed unit ball (`TendstoUniformlyOn`), which avoids a real supremum. The point $x$ is fixed before the almost-sure quantifier, as on the page, so the exceptional null set may depend on $x$. The sample is one i.i.d. sequence: "w.p.1" means for $Q$-almost every sample path, the convergence holds as $N\to\infty$ along the first $N$ terms of that path.
-- source:
--   Shapiro & Homem-de-Mello, On Rate of Convergence of Optimal Solutions of Monte Carlo Approximations of Stochastic Programs, preprint (SPEPS copy, edoc.hu-berlin.de), p. 5, Proposition 2.2, (2.6)

import Mathlib
import Definitions.Def_SAARate_Sharp_Setting

namespace SAARate.Sharp

open MeasureTheory ProbabilityTheory Filter Topology

theorem prop_2_2_eq_2_6 {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : E m → Ω → ℝ)
    (hconv : ∀ ω, ConvexOn ℝ Set.univ (fun x => h x ω))
    (hint : ∀ x, Integrable (h x) P)
    {S : Type*} [MeasurableSpace S] (Q : Measure S) [IsProbabilityMeasure Q]
    (ω : ℕ → S → Ω) (hω : IsIIDSample Q P ω) :
    ∀ x : E m, ∀ᵐ s ∂Q,
      TendstoUniformlyOn (fun (N : ℕ) (d : E m) => dirDeriv (saaObj h (fun j => ω j s) N) x d)
        (fun d => dirDeriv (expectedObj P h) x d) atTop (Metric.closedBall 0 1) := by sorry

end SAARate.Sharp
