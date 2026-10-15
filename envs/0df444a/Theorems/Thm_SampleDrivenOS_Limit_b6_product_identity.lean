-- Prove2me | Theorems.Thm_SampleDrivenOS_Limit_b6_product_identity
-- name    : SampleDrivenOS.Limit.b6_product_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:16.757723+00:00
-- url     : https://prove2.me/theorems/80c8217e-6c50-44a7-974a-fb8b85bfd901
-- title:
--   B.6, p. 33 — for Lemma 6's times, $T_i/t_i^{i-1}=p\gamma_{i-1}$ for $i\ge2$
-- statement:
--   Let $p,\alpha\in(0,1)$, let $(\gamma_k)$ and $(t_k)$ be as in Lemma 6, and $T_i=\prod_{j=1}^i t_j$. Then for every $i\ge2$,
--   $$\frac{T_i}{t_i^{\,i-1}}=p\,\gamma_{i-1}.$$
--
--   This product identity is the step of the proof of Lemma 6 (iii) that evaluates the terms of $\mu_k$ and the right-hand side of (16) for Lemma 6's times.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 33, B.6 (proof of Lemma 6), last display

import Mathlib
import Definitions.Def_SampleDrivenOS_Limit_Setting

open MeasureTheory Filter Topology

namespace SampleDrivenOS.Limit

/-- B.6 (p. 33): for the sequence of Lemma 6 and every `i ≥ 2`,
`T_i / t_i^{i-1} = p γ_{i-1}`. -/
theorem b6_product_identity (p α : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1) (hα : α ∈ Set.Ioo (0:ℝ) 1) :
    ∀ i : ℕ, 2 ≤ i →
      SampleDrivenOS.Structure.thresholdProd (tSeq p α) i / tSeq p α i ^ (i - 1) = p * gammaK p α (i - 1) := by sorry

end SampleDrivenOS.Limit
