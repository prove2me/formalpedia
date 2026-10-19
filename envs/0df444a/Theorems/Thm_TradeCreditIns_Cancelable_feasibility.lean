-- Prove2me | Theorems.Thm_TradeCreditIns_Cancelable_feasibility
-- name    : TradeCreditIns.Cancelable.feasibility
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:42.321343+00:00
-- url     : https://prove2.me/theorems/aa024956-5027-4948-b265-b781a0bd9ebb
-- title:
--   Proof of Proposition 3, step 2 — feasibility of the proposed contract
-- statement:
--   Suppose the outside option is attractive, $r_0\ge(1-\beta_2)r$, and monitoring is efficient, $c\le\phi$, under the paper's standing assumptions and Assumptions 1–2. The proposed contract
--
--   $$
--   \delta=0,\qquad p=f=\frac{c}{\theta_1}+\beta_1r
--   $$
--
--   is feasible: the insurer monitors and cancels coverage at exactly signals 2 and 3, and the supplier ships at exactly signal 1.
--
--   This establishes the behavior that the optimality and full-value claims require.
--
--   **Formalization Note** Signal 1 is index 0. The proposition proof resolves ties by canceling only when the refund is strictly below the expected claim and shipping after cancelation only when credit strictly beats the outside option; the same rules define the Lean decisions. The standing assumptions include $c>0$, $l\ge0$, and $\theta_1>0$.
-- source:
--   Yang, Bakshi & Chen, Trade credit insurance: operational value and contract choice, accepted manuscript (Management Science 67(2), 2021; LBS Research Online eprint 1343), proof of Proposition 3, step 2, p. xii (PDF 44)

import Mathlib
import Definitions.Def_TradeCreditIns_Cancelable_Model

namespace TradeCreditIns.Cancelable

/-- Proof of Proposition 3, step 2, p. xii (PDF 44). -/
theorem feasibility (P : Params) (hS : P.Standing)
    (hA1 : Assumption1 P) (hA2 : Assumption2 P)
    (hcφ : P.c ≤ φ P) (hr0 : (1 - P.β 1) * P.r ≤ P.r0) :
    Admissible P (κstar P) ∧
    (∀ i, Cancels P (κstar P) (P.β i) ↔ i ≠ 0) ∧
    (∀ i, Ships P (κstar P) (P.β i) ↔ i = 0) := by sorry

end TradeCreditIns.Cancelable
