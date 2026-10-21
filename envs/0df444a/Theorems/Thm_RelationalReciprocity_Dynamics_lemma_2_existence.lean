-- Prove2me | Theorems.Thm_RelationalReciprocity_Dynamics_lemma_2_existence
-- name    : RelationalReciprocity.Dynamics.lemma_2_existence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:17:25.173499+00:00
-- url     : https://prove2.me/theorems/58a82e9a-65e7-4e26-92c8-49dd91a1e141
-- title:
--   Lemma 2 (existence), p. 16 — a profit-maximizing path of the reduced problem exists
-- statement:
--   Let $\theta>0$, $\eta\ge0$, $\delta\in(0,1]$ and $2\le T<\infty$. Then there exist paths $(e_t)$, $(w_t)$, $(\Pi_t)$ forming a profit-maximizing path: $\Pi_{T+1}=0$ and, for every period $1\le t\le T$, the pair $(e_t,w_t)$ maximizes the per-period profit
--   $$
--   \pi(e,w)=e\theta-b(e,w)-w
--   $$
--   over $e,w\ge0$ subject to the dynamic enforcement constraint $b(e,w)\le\delta\Pi_{t+1}$, and $\Pi_t=\pi(e_t,w_t)+\delta\Pi_{t+1}$.
--
--   This is the existence claim of Lemma 2, read in the reduced problem the paper states after the lemma. It guarantees that the statements quantified over profit-maximizing paths (Lemma 5, Proposition 1) are not vacuous.
--
--   **Formalization Note.** The other bullets of Lemma 2 ($w_t=w_t^{nd}$, binding (IC), $U_t=\tilde U_t$, sequential optimality) are the reduction from the game to this problem and are built into the model rather than stated.
-- source:
--   Fahn, Reciprocity in Dynamic Employment Relationships, CRC TRR 190 Discussion Paper No. 198 (Nov. 8, 2019), pp. 16–17 (PDF 18–19), Lemma 2 (existence part), in the reduced problem of p. 17

import Mathlib
import Definitions.Def_RelationalReciprocity_Dynamics_Model

namespace RelationalReciprocity.Dynamics

/-- Lemma 2 (existence part), p. 16, read in the reduced problem of p. 17: under the standing
assumptions a profit-maximizing path exists. -/
theorem lemma_2_existence (P : Params) (hP : P.Standing) :
    ∃ e w Pi : ℕ → ℝ, IsOptimalPath P e w Pi := by sorry

end RelationalReciprocity.Dynamics
