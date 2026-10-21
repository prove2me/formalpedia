-- Prove2me | Theorems.Thm_RelationalReciprocity_Dynamics_deviation_effort
-- name    : RelationalReciprocity.Dynamics.deviation_effort
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:17:24.09655+00:00
-- url     : https://prove2.me/theorems/80e73892-d973-43a4-8ff0-e233e4edccd7
-- title:
--   §3.2.1, p. 16 — the deviation effort ẽ = √(ηwθ) uniquely maximizes −e³/3 + ηweθ
-- statement:
--   Let $\theta>0$ and $\eta\ge0$ satisfy the standing assumptions, and let $w\ge0$ be an upfront wage. An agent who responds only to the norm of reciprocity chooses effort to maximize $-e^3/3+\eta we\theta$ over $e\ge0$. The deviation effort
--   $$
--   \tilde e=\sqrt{\eta w\theta}
--   $$
--   is non-negative and is the unique maximizer: for every $e\ge0$ with $e\neq\tilde e$,
--   $$
--   -\frac{e^3}{3}+\eta we\theta<-\frac{\tilde e^3}{3}+\eta w\tilde e\theta .
--   $$
--   Consequently the binding-(IC) bonus $b(e,w)=\frac{e^3}{3}-\eta w\theta e+\frac23(\sqrt{\eta w\theta})^3$ is non-negative for every $e\ge0$.
--
--   The deviation effort is the agent's outside effort after a deviation; the gap between it and the effort the principal asks for is what relational incentives have to pay for.
-- source:
--   Fahn, Reciprocity in Dynamic Employment Relationships, CRC TRR 190 Discussion Paper No. 198 (Nov. 8, 2019), p. 16 (PDF 18), §3.2.1

import Mathlib
import Definitions.Def_RelationalReciprocity_Dynamics_Model

namespace RelationalReciprocity.Dynamics

/-- §3.2.1, p. 16: for a wage `w ≥ 0`, the deviation effort `ẽ = √(ηwθ)` is the unique maximizer
of `−e³/3 + ηweθ` over `e ≥ 0`; consequently the binding-(IC) bonus is non-negative. -/
theorem deviation_effort (P : Params) (hP : P.Standing) (w : ℝ) (hw : 0 ≤ w) :
    0 ≤ devEffort P w ∧
    (∀ e : ℝ, 0 ≤ e → e ≠ devEffort P w →
      -e ^ 3 / 3 + P.η * w * e * P.θ < -devEffort P w ^ 3 / 3 + P.η * w * devEffort P w * P.θ) ∧
    (∀ e : ℝ, 0 ≤ e → 0 ≤ bonus P e w) := by sorry

end RelationalReciprocity.Dynamics
