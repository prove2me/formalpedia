-- Prove2me | Theorems.Thm_PrivLearn_LocalSim_hoeffding_display
-- name    : PrivLearn.LocalSim.hoeffding_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:10.936225+00:00
-- url     : https://prove2.me/theorems/92f3c758-fae2-4a4f-b4fb-033c03064dd0
-- title:
--   Proof of Lemma 5.6, p. 20 — Hoeffding for the empirical mean of a [−b, b]-valued query
-- statement:
--   Let $P$ be a probability distribution on $D$, let $g:D\to[-b,b]$ be measurable with $b>0$, write $v=\mathbb E_{u\sim P}[g(u)]$, and let $\tau>0$. If $u_1,\dots,u_n$ are i.i.d. from $P$, then
--   $$\Pr\Bigl[\Bigl|\frac1n\sum_{i=1}^n g(u_i)-v\Bigr|\ge\frac\tau2\Bigr]\le 2\exp\Bigl(-\frac{\tau^2n}{8b^2}\Bigr).$$
--
--   This is the Chernoff–Hoeffding bound (Theorem A.2) with range $[-b,b]$ and deviation $\tau/2$; it controls the sampling error of $\mathcal A_g$ in the proof of Lemma 5.6.
--
--   **Formalization Note.** The statement is for every $n\in\mathbb N$; at $n=0$ the right-hand side is $2$ and the bound is trivial.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 20, proof of Lemma 5.6, first display (instance of Theorem A.2, p. 35)

import Mathlib

namespace PrivLearn.LocalSim

open MeasureTheory

/-- Proof of Lemma 5.6 (p. 20), first display: for i.i.d. `u_1, …, u_n ∼ P` and a measurable
`g : Dom → [−b, b]` with mean `v = E_{u∼P}[g(u)]`,
`Pr[|(1/n) ∑ g(u_i) − v| ≥ τ/2] ≤ 2 exp(−τ² n / (8 b²))`. -/
theorem hoeffding_display {Dom : Type*} [MeasurableSpace Dom] (P : Measure Dom)
    [IsProbabilityMeasure P] (g : Dom → ℝ) (hgm : Measurable g) (b τ : ℝ) (hb : 0 < b)
    (hτ : 0 < τ) (hg : ∀ u, |g u| ≤ b) (n : ℕ) :
    (Measure.pi fun _ : Fin n => P)
        {u | τ / 2 ≤ |(1 / (n : ℝ)) * ∑ i, g (u i) - ∫ x, g x ∂P|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(τ ^ 2 * n) / (8 * b ^ 2))) := by sorry

end PrivLearn.LocalSim
