-- Prove2me | Theorems.Thm_RelationalReciprocity_Dynamics_proposition_1
-- name    : RelationalReciprocity.Dynamics.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:17:23.316085+00:00
-- url     : https://prove2.me/theorems/8febf488-fd5a-47c7-bf9d-c7c6b22c94e3
-- title:
--   Proposition 1, p. 20 — along the optimal path effort and bonus weakly decrease and the wage weakly increases, with strict changes propagating
-- statement:
--   Let $\theta>0$, $\eta\ge0$, $\delta\in(0,1]$ and $2\le T<\infty$, and let $(e_t,w_t,\Pi_t)$ be any profit-maximizing path of the reduced problem, with bonuses $b_t=b(e_t,w_t)=\frac{e_t^3}{3}-\eta w_t\theta e_t+\frac23(\sqrt{\eta w_t\theta})^3$. Then:
--
--   1. effort is weakly decreasing: $e_t\le e_{t-1}$ for $2\le t\le T$;
--   2. for $2\le t$ with $t+1\le T$: $e_t<e_{t-1}$ implies $e_{t+1}<e_t$, and $e_{t+1}=e_t$ implies $e_t=e_{t-1}$;
--   3. the wage is weakly increasing and the bonus weakly decreasing: $w_t\ge w_{t-1}$ and $b_t\le b_{t-1}$ for $2\le t\le T$;
--   4. for $2\le t$ with $t+1\le T$: $w_t>w_{t-1}$ and $b_t<b_{t-1}$ imply $w_{t+1}>w_t$ and $b_{t+1}<b_t$; and $w_{t+1}=w_t$ and $b_{t+1}=b_t$ imply $w_t=w_{t-1}$ and $b_t=b_{t-1}$.
--
--   Over the course of employment, relational incentives (the bonus) are gradually replaced by reciprocity-based incentives (the upfront wage), and the substitution is incomplete, so effort falls. Effort, wage and bonus are constant in an initial phase and change strictly in every period of the final phase.
--
--   **Formalization Note.** The model is the reduced per-period problem of p. 17, not the paper's game. The statement holds for every profit-maximizing path. The paper prints the last implication as "$w_{t+1}=w_t$ and $b_{t+1}=b_t$ imply $w_{t+1}=w_t$ and $b_t=b_{t-1}$", which repeats its own premise; the statement uses $w_t=w_{t-1}$, in parallel with the effort sentence and the paper's proof. The third paragraph of the proposition ("total compensation might increase or decrease") makes no claim and is not stated.
-- source:
--   Fahn, Reciprocity in Dynamic Employment Relationships, CRC TRR 190 Discussion Paper No. 198 (Nov. 8, 2019), p. 20 (PDF 22), Proposition 1, paragraphs 1–2 (index of the last clause corrected); proof pp. 42–44 (PDF 44–46)

import Mathlib
import Definitions.Def_RelationalReciprocity_Dynamics_Model

namespace RelationalReciprocity.Dynamics

/-- Proposition 1, p. 20, paragraphs 1–2 (with the index of the last clause corrected): along every
profit-maximizing path effort and bonus weakly decrease and the wage weakly increases; a strict
change propagates to the next period, and no change propagates to the previous period. -/
theorem proposition_1 (P : Params) (hP : P.Standing) (e w Pi : ℕ → ℝ)
    (hpath : IsOptimalPath P e w Pi) :
    (∀ t : ℕ, 2 ≤ t → t ≤ P.T → e t ≤ e (t - 1)) ∧
    (∀ t : ℕ, 2 ≤ t → t + 1 ≤ P.T →
        (e t < e (t - 1) → e (t + 1) < e t) ∧ (e (t + 1) = e t → e t = e (t - 1))) ∧
    (∀ t : ℕ, 2 ≤ t → t ≤ P.T →
        w (t - 1) ≤ w t ∧ bonus P (e t) (w t) ≤ bonus P (e (t - 1)) (w (t - 1))) ∧
    (∀ t : ℕ, 2 ≤ t → t + 1 ≤ P.T →
        (w (t - 1) < w t ∧ bonus P (e t) (w t) < bonus P (e (t - 1)) (w (t - 1)) →
            w t < w (t + 1) ∧ bonus P (e (t + 1)) (w (t + 1)) < bonus P (e t) (w t)) ∧
        (w (t + 1) = w t ∧ bonus P (e (t + 1)) (w (t + 1)) = bonus P (e t) (w t) →
            w t = w (t - 1) ∧ bonus P (e t) (w t) = bonus P (e (t - 1)) (w (t - 1)))) := by sorry

end RelationalReciprocity.Dynamics
