-- Prove2me | Theorems.Thm_RelationalReciprocity_Dynamics_lemma_5
-- name    : RelationalReciprocity.Dynamics.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:17:32.099684+00:00
-- url     : https://prove2.me/theorems/727d1ebf-38f4-4162-85ca-6e241647dd20
-- title:
--   Lemma 5 (last part), p. 19 — on-path profits strictly decline: Πₜ₋₁ > Πₜ
-- statement:
--   Let $\theta>0$, $\eta>0$ and the standing assumptions hold, and let $(e_t,w_t,\Pi_t)$ be a profit-maximizing path. Then the principal's continuation profits strictly decrease over time:
--   $$
--   \Pi_{t-1}>\Pi_t\qquad\text{for all }2\le t\le T .
--   $$
--
--   Declining continuation profits tighten the dynamic enforcement constraint period by period; this drives the dynamics of Proposition 1.
--
--   **Formalization Note.** The paper writes "for all $t\le T$"; the range starts at $t=2$ because $\Pi_0$ is not defined. The hypothesis $\eta>0$ is added: at $\eta=0$ every profit is $0$ and the strict inequality fails.
-- source:
--   Fahn, Reciprocity in Dynamic Employment Relationships, CRC TRR 190 Discussion Paper No. 198 (Nov. 8, 2019), p. 19 (PDF 21), Lemma 5, last sentence; proof pp. 41–42 (PDF 43–44)

import Mathlib
import Definitions.Def_RelationalReciprocity_Dynamics_Model

namespace RelationalReciprocity.Dynamics

/-- Lemma 5 (last part), p. 19: along a profit-maximizing path, `Π_{t−1} > Π_t` for `2 ≤ t ≤ T`. -/
theorem lemma_5 (P : Params) (hP : P.Standing) (hη : 0 < P.η) (e w Pi : ℕ → ℝ)
    (hpath : IsOptimalPath P e w Pi) :
    ∀ t : ℕ, 2 ≤ t → t ≤ P.T → Pi t < Pi (t - 1) := by sorry

end RelationalReciprocity.Dynamics
