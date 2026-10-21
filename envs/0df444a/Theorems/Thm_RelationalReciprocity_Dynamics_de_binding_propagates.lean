-- Prove2me | Theorems.Thm_RelationalReciprocity_Dynamics_de_binding_propagates
-- name    : RelationalReciprocity.Dynamics.de_binding_propagates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:17:29.872632+00:00
-- url     : https://prove2.me/theorems/c36fef2f-978b-4de5-a267-91ce864e61f1
-- title:
--   §3.2.3, p. 20 — once (DE) binds it binds in all later periods; slack propagates to all earlier periods
-- statement:
--   Let the standing assumptions hold and let $(e_t,w_t,\Pi_t)$ be a profit-maximizing path. For periods $1\le t<s\le T$:
--
--   1. if the dynamic enforcement constraint binds in period $t$ (no first-best pair satisfies $b(e,w)\le\delta\Pi_{t+1}$), it also binds in period $s$;
--   2. if it is slack in period $s$ (some first-best pair satisfies $b(e,w)\le\delta\Pi_{s+1}$), it is also slack in period $t$.
--
--   The relationship therefore splits into an initial phase in which enforcement is not a constraint, followed by a final phase in which it binds in every period.
--
--   **Formalization Note.** Binding is expressed without multipliers, as the failure of the first-best pairs to satisfy the period's constraint; the paper's proof argues through the multipliers $\lambda_{DE_t}$. The statement needs no $\eta>0$: at $\eta=0$ all bounds are $0$ and both claims are immediate.
-- source:
--   Fahn, Reciprocity in Dynamic Employment Relationships, CRC TRR 190 Discussion Paper No. 198 (Nov. 8, 2019), p. 20 (PDF 22), §3.2.3; proof of Proposition 1, pp. 42–43 (PDF 44–45)

import Mathlib
import Definitions.Def_RelationalReciprocity_Dynamics_Model

namespace RelationalReciprocity.Dynamics

/-- §3.2.3, p. 20: along a profit-maximizing path, if the (DE) constraint binds in a period it
binds in every later period, and if it is slack in a period it is slack in every earlier period. -/
theorem de_binding_propagates (P : Params) (hP : P.Standing) (e w Pi : ℕ → ℝ)
    (hpath : IsOptimalPath P e w Pi) :
    (∀ t s : ℕ, 1 ≤ t → t < s → s ≤ P.T →
      ¬ DESlack P (P.δ * Pi (t + 1)) → ¬ DESlack P (P.δ * Pi (s + 1))) ∧
    (∀ t s : ℕ, 1 ≤ t → t < s → s ≤ P.T →
      DESlack P (P.δ * Pi (s + 1)) → DESlack P (P.δ * Pi (t + 1))) := by sorry

end RelationalReciprocity.Dynamics
