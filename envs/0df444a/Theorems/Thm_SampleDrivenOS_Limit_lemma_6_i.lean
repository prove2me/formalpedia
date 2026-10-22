-- Prove2me | Theorems.Thm_SampleDrivenOS_Limit_lemma_6_i
-- name    : SampleDrivenOS.Limit.lemma_6_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:14.996096+00:00
-- url     : https://prove2.me/theorems/b961163e-0061-433f-bca9-6a158342013a
-- title:
--   Lemma 6 (i) — the times $t_1=p$, $t_2=pe^{\alpha(1-p)^2/p}$, (17) are increasing
-- statement:
--   Let $p,\alpha\in(0,1)$, let $\gamma_k=1-\alpha+\alpha[kp^{k-1}-(k-1)p^k]$, and let $t_1=p$, $t_2=p\exp(\alpha(1-p)^2/p)$ and, for $k\ge2$, $t_{k+1}>0$ with
--   $$\Bigl(\frac{t_k}{t_{k+1}}\Bigr)^{k-1}=\frac{\gamma_k}{\gamma_{k-1}}. \qquad(17)$$
--   Then the sequence is increasing:
--   $$t_k\le t_{k+1}\qquad\text{for all }k\ge1 .$$
--
--   Monotonicity is what makes the times admissible thresholds for the form (12).
--
--   **Formalization Note** "Increasing" is rendered as $t_k\le t_{k+1}$, the inequality the paper's proof establishes; for these $p,\alpha$ the inequalities are in fact strict. All $\gamma_k$ lie in $[1-\alpha,1]$, so (17) has the unique positive solution $t_{k+1}=t_k(\gamma_{k-1}/\gamma_k)^{1/(k-1)}$, which is the definition used.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 16, Lemma 6 (i), (17)

import Mathlib
import Definitions.Def_SampleDrivenOS_Limit_Setting

open MeasureTheory Filter Topology

namespace SampleDrivenOS.Limit

/-- Lemma 6 (i) (p. 16): for `p, α ∈ (0, 1)`, the sequence `(t_k)_{k ≥ 1}` defined by
`t_1 = p`, `t_2 = p exp(α(1-p)²/p)` and (17) is increasing (`t_k ≤ t_{k+1}` for all `k ≥ 1`). -/
theorem lemma_6_i (p α : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1) (hα : α ∈ Set.Ioo (0:ℝ) 1) :
    ∀ k : ℕ, 1 ≤ k → tSeq p α k ≤ tSeq p α (k + 1) := by sorry

end SampleDrivenOS.Limit
