-- Prove2me | Theorems.Thm_SampleDrivenOS_Limit_b6_mu_closed_form
-- name    : SampleDrivenOS.Limit.b6_mu_closed_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:15.761844+00:00
-- url     : https://prove2.me/theorems/8ef63a5c-95de-4bb2-8dd8-d3cfb0fb64a9
-- title:
--   B.6, p. 34 — for Lemma 6's times, $\mu_k=p(1-\alpha+\alpha p^{k-2})/(k-2)$ for $k\ge3$
-- statement:
--   Let $p,\alpha\in(0,1)$, let $(t_k)$ be the times of Lemma 6, $T_i=\prod_{j=1}^i t_j$, and $\mu_k=\sum_{i=k}^{\infty}\frac{T_i}{t_i^{i-1}}\cdot\frac{1}{(i-2)(i-1)}$. Then for every $k\ge3$,
--   $$\mu_k=\frac{p\,(1-\alpha+\alpha p^{k-2})}{k-2}.$$
--
--   With this closed form, (15) and (16) of Lemma 5 become direct algebraic identities for Lemma 6's times.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 34, B.6 (proof of Lemma 6), first display

import Mathlib
import Definitions.Def_SampleDrivenOS_Limit_Setting

open MeasureTheory Filter Topology

namespace SampleDrivenOS.Limit

/-- B.6 (p. 34): for the sequence of Lemma 6 and every `k ≥ 3`,
`µ_k = p(1 - α + α p^{k-2}) / (k - 2)`. -/
theorem b6_mu_closed_form (p α : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1) (hα : α ∈ Set.Ioo (0:ℝ) 1) :
    ∀ k : ℕ, 3 ≤ k →
      mu (tSeq p α) k = p * (1 - α + α * p ^ (k - 2)) / ((k : ℝ) - 2) := by sorry

end SampleDrivenOS.Limit
