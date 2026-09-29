-- Prove2me | Theorems.Thm_PolyakJuditsky_Averaging_step_size_mul_t_tendsto_top
-- name    : PolyakJuditsky.Averaging.step_size_mul_t_tendsto_top
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:38:21.602988+00:00
-- url     : https://prove2.me/theorems/d597f47e-614c-45b4-a4dc-66fba4a89bbe
-- title:
--   Lemma 1, Part 2 — $t\gamma_t\to\infty$
-- statement:
--   Let $(\gamma_t)_{t\ge1}$ be step sizes satisfying condition (4) of Assumption 2.2: $\gamma_t>0$ for $t\ge1$, $\gamma_t\to0$, and
--   $$\frac{\gamma_t-\gamma_{t+1}}{\gamma_t}=o(\gamma_t)\qquad(t\to\infty).$$
--   Then
--   $$t\,\gamma_t\to\infty\qquad(t\to\infty).$$
--
--   The step sizes may therefore decrease to zero, but more slowly than $1/t$. The proof of Theorem 2 uses this to get $\sum_t\gamma_t=\infty$ (p. 849).
--
--   **Formalization Note** The statement is Part 2 of the proof of Lemma 1; of the lemma's hypotheses only condition (4) is used, so the eigenvalue hypothesis on $A$ is not included.
-- source:
--   Polyak, Juditsky, Acceleration of stochastic approximation by averaging, SIAM J. Control Optim. 30 (1992), p. 845, proof of Lemma 1, Part 2

import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model

open Filter Topology

namespace PolyakJuditsky.Averaging

/-- Lemma 1, proof Part 2 (p. 845): under condition (4) of Assumption 2.2, `t γ_t → ∞`. -/
theorem step_size_mul_t_tendsto_top (γ : ℕ → ℝ) (hγ : StepCondition4 γ) :
    Tendsto (fun t : ℕ => (t : ℝ) * γ t) atTop atTop := by sorry

end PolyakJuditsky.Averaging
