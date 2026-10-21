-- Prove2me | Theorems.Thm_RelationalReciprocity_Dynamics_final_period_comparison
-- name    : RelationalReciprocity.Dynamics.final_period_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:17:24.072257+00:00
-- url     : https://prove2.me/theorems/de22582a-5ea4-4e74-b7fd-6bf21902cb83
-- title:
--   Proof of Proposition 1, p. 43 — e*_T < e*_t and w_T > w_t for every t < T
-- statement:
--   Let $\theta>0$, $\eta>0$ and the standing assumptions hold, and let $(e_t,w_t,\Pi_t)$ be a profit-maximizing path. Then for every period $1\le t<T$,
--   $$
--   e_T<e_t\qquad\text{and}\qquad w_t<w_T .
--   $$
--
--   In the last period the spot contract ($e_T=\eta\theta^2/2$, $w_T=\eta\theta^3/4$) has strictly lower effort and a strictly higher wage than any earlier period.
--
--   **Formalization Note.** The paper derives the inequalities from the closed forms through the equivalences "$\Leftrightarrow\eta^2\theta^3(1+\lambda)<1+\eta^2\theta^3(1+\lambda)$" and "$\Leftrightarrow2\eta^2\theta^3(1+\lambda)>1$"; the statement asserts the inequalities themselves for every earlier period, whichever branch (zero or positive wage) that period is on.
-- source:
--   Fahn, Reciprocity in Dynamic Employment Relationships, CRC TRR 190 Discussion Paper No. 198 (Nov. 8, 2019), p. 43 (PDF 45), proof of Proposition 1

import Mathlib
import Definitions.Def_RelationalReciprocity_Dynamics_Model

namespace RelationalReciprocity.Dynamics

/-- Proof of Proposition 1, p. 43: along a profit-maximizing path, effort in the last period `T`
is below, and the wage in period `T` above, effort and wage in every earlier period. -/
theorem final_period_comparison (P : Params) (hP : P.Standing) (hη : 0 < P.η) (e w Pi : ℕ → ℝ)
    (hpath : IsOptimalPath P e w Pi) :
    ∀ t : ℕ, 1 ≤ t → t < P.T → e P.T < e t ∧ w t < w P.T := by sorry

end RelationalReciprocity.Dynamics
