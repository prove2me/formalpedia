-- Prove2me | Theorems.Thm_RecallTesting_Duopoly_eq_A3_no_firm_test
-- name    : RecallTesting.Duopoly.eq_A3_no_firm_test
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:28.767477+00:00
-- url     : https://prove2.me/theorems/df69bbd4-cc96-4efa-8a6f-5d422be5d467
-- title:
--   (A.3), p. 37 — not testing is a best response to a non-tester iff θ ∈ [θ̃nt_lower, θ̃nt_upper]
-- statement:
--   Assume the standing assumptions $V,B,\rho>0$, $\delta\in(0,1]$, $\gamma,\theta\in(0,1)$. Write $b=(V+B)(1-\gamma)\gamma-(3+\gamma)^2\rho$ and
--   $$D=b^2-\frac{4VB(V+B)^2(5-\gamma)\gamma(3+\gamma)^2}{(3V+4B)^2},\qquad \underline{\tilde\theta}^{nt},\ \overline{\tilde\theta}^{nt}=\frac{b\mp\sqrt D}{2(V+B)(5-\gamma)\gamma}.$$
--   Then, against a rival that does not test, not testing is at least as profitable as testing exactly when $\theta$ lies in the interval $\tilde\theta^{nt}$:
--   $$\Pi^{0,0}\ \ge\ \Pi^{1,0}\iff D\ge 0\ \text{ and }\ \underline{\tilde\theta}^{nt}\le\theta\le\overline{\tilde\theta}^{nt}.$$
--
--   This is the condition for the no-firm-test equilibrium.
--
--   **Formalization Note** "$\theta\in\tilde\theta^{nt}$" presupposes that the two roots are real; the clause $D\ge 0$ makes that explicit (for $D<0$ the interval is empty and no $\theta$ qualifies). Both payoffs are the model's, not closed forms.
-- source:
--   Kim, Koenigsberg & Ofek, I Don’t “Recall”, SSRN working paper 3492105 (Nov. 2019), p. 37 (PDF 38), proof of Proposition 2, No-firm-test equilibrium, display before (A.3)

import Mathlib
import Definitions.Def_RecallTesting_Duopoly_Model

namespace RecallTesting.Duopoly

theorem eq_A3_no_firm_test (P : Params) (hS : P.Standing) :
    payoff P true false ≤ payoff P false false ↔
      0 ≤ discNT P ∧ thetaNTlo P ≤ P.θ ∧ P.θ ≤ thetaNThi P := by sorry

end RecallTesting.Duopoly
