-- Prove2me | Theorems.Thm_SampleDrivenOS_Limit_lemma_6_ii
-- name    : SampleDrivenOS.Limit.lemma_6_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:25.500913+00:00
-- url     : https://prove2.me/theorems/ab7aef9b-9286-4158-82f4-10a7d2e0bcaa
-- title:
--   Lemma 6 (ii) — $\lim_k t_k\le1$ if and only if (18), with $\lim_k t_k=1$ under equality
-- statement:
--   Let $p,\alpha\in(0,1)$, and let $(\gamma_k)$ and $(t_k)$ be as in Lemma 6. Then $t_k$ converges to a finite limit $L$, and
--   $$L\le1\iff \ln p+\frac{\alpha(1-p)^2}{p}\le\sum_{i=1}^{\infty}\frac{\ln\gamma_{i+1}}{i(i+1)} . \qquad(18)$$
--   Moreover $L=1$ when equality holds in (18).
--
--   Condition (18) is exactly what is needed for the times of Lemma 6 to stay inside the horizon $[p,1]$; with equality it is equation (19) defining $\tilde\alpha(p)$.
--
--   **Formalization Note** The paper writes $\lim_{k\to\infty}t_k$; the statement asserts the limit exists in $\mathbb R$ (the proof shows $\ln t_k$ converges) and names it $L$. The series is written with its index shifted by one; it converges absolutely because every $\gamma_{i+1}\in[1-\alpha,1]$.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 16, Lemma 6 (ii), (18)

import Mathlib
import Definitions.Def_SampleDrivenOS_Limit_Setting

open MeasureTheory Filter Topology

namespace SampleDrivenOS.Limit

/-- Lemma 6 (ii) (p. 16): for `p, α ∈ (0, 1)`, the sequence `(t_k)` of Lemma 6 has a finite
limit `L`, and `L ≤ 1` if and only if (18)
`ln p + α(1-p)²/p ≤ ∑_{i=1}^{∞} ln(γ_{i+1}) / (i(i+1))`; moreover `L = 1` when equality holds in
(18). The series is written with its index shifted by one. -/
theorem lemma_6_ii (p α : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1) (hα : α ∈ Set.Ioo (0:ℝ) 1) :
    ∃ L : ℝ, Tendsto (fun k => tSeq p α k) atTop (𝓝 L) ∧
      (L ≤ 1 ↔ Real.log p + α * (1 - p) ^ 2 / p ≤
          ∑' i : ℕ, Real.log (gammaK p α (i + 2)) / (((i : ℝ) + 1) * ((i : ℝ) + 2))) ∧
      (Real.log p + α * (1 - p) ^ 2 / p =
          ∑' i : ℕ, Real.log (gammaK p α (i + 2)) / (((i : ℝ) + 1) * ((i : ℝ) + 2)) →
        L = 1) := by sorry

end SampleDrivenOS.Limit
