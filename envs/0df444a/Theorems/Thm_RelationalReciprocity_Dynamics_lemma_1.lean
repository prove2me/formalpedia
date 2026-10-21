-- Prove2me | Theorems.Thm_RelationalReciprocity_Dynamics_lemma_1
-- name    : RelationalReciprocity.Dynamics.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:17:42.68047+00:00
-- url     : https://prove2.me/theorems/76217207-3010-4858-bfe8-4a2680623ce2
-- title:
--   Lemma 1, p. 14 — the reciprocity spot contract has w = ηθ³/4, e* = ηθ²/2, π = ηθ³/4
-- statement:
--   Let $\theta>0$, $\eta>0$ and the standing assumptions hold. Consider the period problem with dynamic enforcement bound $0$: maximize $\pi(e,w)=e\theta-b(e,w)-w$ over $e,w\ge0$ subject to $b(e,w)\le0$. This is the reciprocity spot contract of §3.1, offered in the final period $T$. Its optimal pairs are exactly
--   $$
--   w=\frac{\eta\theta^3}{4},\qquad e^*=\frac{\eta\theta^2}{2}.
--   $$
--   At this pair the bonus is $b=0$, the principal's profit is $\pi=\eta\theta^3/4$, and the agent's utility is
--   $$
--   u=\frac{\eta\theta^3}{4}+\frac{\eta^3\theta^6}{12}.
--   $$
--
--   The spot contract fixes the last period of every profit-maximizing path and is the benchmark against which earlier periods are compared.
--
--   **Formalization Note.** The paper's spot problem maximizes $e^*\theta-w$ with $e^*=\sqrt{\eta w\theta}$; in the reduced problem the constraint $b(e,w)\le0$ forces $e=\sqrt{\eta w\theta}$ and $b=0$, so the two problems coincide. The hypothesis $\eta>0$ is added because the formulas give the degenerate pair $(0,0)$ at $\eta=0$.
-- source:
--   Fahn, Reciprocity in Dynamic Employment Relationships, CRC TRR 190 Discussion Paper No. 198 (Nov. 8, 2019), p. 14 (PDF 16), Lemma 1

import Mathlib
import Definitions.Def_RelationalReciprocity_Dynamics_Model

namespace RelationalReciprocity.Dynamics

/-- Lemma 1, p. 14: the reciprocity spot contract (the period problem with (DE) bound `0`) has
`w = ηθ³/4`, `e* = ηθ²/2`, hence `b = 0`, `π = ηθ³/4` and `u = ηθ³/4 + η³θ⁶/12`. -/
theorem lemma_1 (P : Params) (hP : P.Standing) (hη : 0 < P.η) :
    (∀ e w : ℝ, IsOptimal P 0 e w ↔ w = P.η * P.θ ^ 3 / 4 ∧ e = P.η * P.θ ^ 2 / 2) ∧
    bonus P (P.η * P.θ ^ 2 / 2) (P.η * P.θ ^ 3 / 4) = 0 ∧
    profit P (P.η * P.θ ^ 2 / 2) (P.η * P.θ ^ 3 / 4) = P.η * P.θ ^ 3 / 4 ∧
    agentUtility P (P.η * P.θ ^ 2 / 2) (P.η * P.θ ^ 3 / 4) 0 =
      P.η * P.θ ^ 3 / 4 + P.η ^ 3 * P.θ ^ 6 / 12 := by sorry

end RelationalReciprocity.Dynamics
