-- Prove2me | Theorems.Thm_RecallTesting_Duopoly_eq_A4_dual_firm_test
-- name    : RecallTesting.Duopoly.eq_A4_dual_firm_test
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:28.638047+00:00
-- url     : https://prove2.me/theorems/9c177721-95d6-4ace-a0aa-1bb038e15ec5
-- title:
--   (A.4), p. 37 — testing is a best response to a tester iff θ ≥ θ̃st (with a positive denominator)
-- statement:
--   Assume the standing assumptions $V,B,\rho>0$, $\delta\in(0,1]$, $\gamma,\theta\in(0,1)$. Write
--   $$N=(V+B)\big(4B(V+B)(3+\gamma)^2\delta-(3V+4B)^2(1-\gamma)\gamma\big)+(3V+4B)^2(3+\gamma)^2\rho,\qquad \tilde\theta^{st}=\frac{4B(V+B)^2(3+\gamma)^2}{N}.$$
--   Then, against a rival that tests, testing is at least as profitable as not testing exactly when $\theta$ is at least the cutoff:
--   $$\Pi^{1,1}=0\ \ge\ \Pi^{0,1}\iff N>0\ \text{ and }\ \theta\ge\tilde\theta^{st}.$$
--
--   This is the condition for the dual-firm-test equilibrium.
--
--   **Formalization Note** The page writes the equivalence as $\theta\ge\tilde\theta^{st}$, which divides by $N$; when $N\le 0$ (small $\rho$) no $\theta$ satisfies the inequality, and the clause $N>0$ records this.
-- source:
--   Kim, Koenigsberg & Ofek, I Don’t “Recall”, SSRN working paper 3492105 (Nov. 2019), p. 37 (PDF 38), proof of Proposition 2, Dual-firm-test equilibrium, (A.4)

import Mathlib
import Definitions.Def_RecallTesting_Duopoly_Model

namespace RecallTesting.Duopoly

theorem eq_A4_dual_firm_test (P : Params) (hS : P.Standing) :
    payoff P false true ≤ payoff P true true ↔ 0 < denST P ∧ thetaST P ≤ P.θ := by sorry

end RecallTesting.Duopoly
