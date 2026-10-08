-- Prove2me | Theorems.Thm_SmoothedSimplex_Shadow_measure_P
-- name    : SmoothedSimplex.Shadow.measure_P
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T13:17:36.978185+00:00
-- url     : https://prove2.me/theorems/655ff3db-d25c-463e-b0a7-0a84b3251437
-- title:
--   Proposition 4.0.5 — $\Pr[(a_1,\dots,a_n)\in P]\ge 1-n^{-2.9d+1}$
-- statement:
--   Let $d\ge3$ and $n>d$, let $0<\sigma\le 1/(3\sqrt{d\ln n})$, and let $a_1,\dots,a_n$ be independent Gaussian random vectors in $\mathbb R^d$ of standard deviation $\sigma$ centered at points $\bar a_1,\dots,\bar a_n$ of norm at most $1$. Then
--
--   $$
--   \Pr\big[(a_1,\dots,a_n)\in P\big]\ \ge\ 1-n\big(n^{-2.9d}\big)=1-n^{-2.9d+1},
--   $$
--
--   where $P$ is the event that $\|a_i\|\le 2$ for every $i$.
--
--   The analysis of the Shadow Size Theorem conditions on $P$; this proposition shows that the complement of $P$ costs at most an additive $1$ in the expected shadow size.
--
--   **Formalization Note** The page states the proposition without hypotheses; it holds in Section 4 under the hypotheses of Theorem 4.0.1 together with the reduction $\sigma\le1/(3\sqrt{d\ln n})$ made on the first line of the proof of Theorem 4.0.1 (p. 39). These are the hypotheses here.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Proposition 4.0.5, printed p. 38 (PDF p. 38); hypotheses from Theorem 4.0.1 and the proof's first line, p. 39

import Mathlib
import Definitions.Def_SmoothedSimplex_Shadow_gaussian
import Definitions.Def_SmoothedSimplex_Shadow_setP

namespace SmoothedSimplex.Shadow

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

/-- **Proposition 4.0.5 (Measure of P)** (Spielman & Teng, arXiv:cs/0111050v7, Proposition 4.0.5,
printed p. 38, PDF p. 38): `Pr[(a₁, …, aₙ) ∈ P] ≥ 1 − n(n^{−2.9d}) = 1 − n^{−2.9d+1}`, where
`P = {‖aᵢ‖ ≤ 2 for all i}` (Definition 4.0.4).

**Formalization Note.** The page states no hypotheses; the proposition lives in §4 under the
hypotheses of Theorem 4.0.1 (`d ≥ 3`, `n > d`, `aᵢ` independent Gaussians of standard
deviation `σ` centered at points of norm at most 1) and the reduction `σ ≤ 1/(3√(d ln n))` made
on the first line of its proof (p. 39). These are the binders here. The joint law of
`a₁, …, aₙ` is the product of the `gaussian (ā i) σ`. -/
theorem measure_P {d n : ℕ} (hd : 3 ≤ d) (hn : d < n) (σ : ℝ) (hσ : 0 < σ)
    (hσ' : σ ≤ 1 / (3 * Real.sqrt ((d : ℝ) * Real.log n)))
    (abar : Fin n → EuclideanSpace ℝ (Fin d)) (habar : ∀ i, ‖abar i‖ ≤ 1) :
    ENNReal.ofReal (1 - (n : ℝ) ^ (-(29 / 10 : ℝ) * d + 1)) ≤
      Measure.pi (fun i => gaussian (abar i) σ) setP := by sorry

end SmoothedSimplex.Shadow
