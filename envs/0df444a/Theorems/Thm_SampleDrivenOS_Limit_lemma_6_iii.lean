-- Prove2me | Theorems.Thm_SampleDrivenOS_Limit_lemma_6_iii
-- name    : SampleDrivenOS.Limit.lemma_6_iii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:45.069997+00:00
-- url     : https://prove2.me/theorems/2cc8a39e-8bbc-4498-b481-b37179001a99
-- title:
--   Lemma 6 (iii) — under (18), the threshold rule built from Lemma 6's times is feasible for SDCLP$_p$ with value $\alpha$
-- statement:
--   Let $p,\alpha\in(0,1)$ satisfy (18):
--   $$\ln p+\frac{\alpha(1-p)^2}{p}\le\sum_{i=1}^{\infty}\frac{\ln\gamma_{i+1}}{i(i+1)},$$
--   where $\gamma_k=1-\alpha+\alpha[kp^{k-1}-(k-1)p^k]$. Let $(t_k)$ be the times of Lemma 6 and $q$ the threshold stopping rule (12) built from them. Then $(q,\alpha)$ is feasible for SDCLP$_p$.
--
--   Consequently $\alpha(p)\ge\alpha$ for every such $\alpha$; this is the lower half of Theorem 8.
--
--   **Formalization Note** Hypothesis (18) is not in the printed statement of (iii); it is the condition under which the paper applies it ("as long as (18) holds for values $p,\alpha\in(0,1)$, we obtain a solution", p. 17). Without it the times exceed $1$, $q$ vanishes on $[p,1]$ for large ranks, and (11) fails, so (iii) is false as printed in isolation.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 17, Lemma 6 (iii) and the sentence following it

import Mathlib
import Definitions.Def_SampleDrivenOS_Limit_Setting

open MeasureTheory Filter Topology

namespace SampleDrivenOS.Limit

/-- Lemma 6 (iii) (p. 17): for `p, α ∈ (0, 1)` satisfying (18), the function `q` defined from
the sequence `(t_k)` of Lemma 6 as in (12) makes `(q, α)` feasible for SDCLP_p. (18) is the
condition under which the paper applies (iii), stated in the sentence after the lemma. -/
theorem lemma_6_iii (p α : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1) (hα : α ∈ Set.Ioo (0:ℝ) 1)
    (h18 : Real.log p + α * (1 - p) ^ 2 / p ≤
      ∑' i : ℕ, Real.log (gammaK p α (i + 2)) / (((i : ℝ) + 1) * ((i : ℝ) + 2))) :
    IsSDFeasible p (thresholdQ (tSeq p α)) α := by sorry

end SampleDrivenOS.Limit
