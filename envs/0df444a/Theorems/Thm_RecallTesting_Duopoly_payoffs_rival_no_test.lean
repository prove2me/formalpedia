-- Prove2me | Theorems.Thm_RecallTesting_Duopoly_payoffs_rival_no_test
-- name    : RecallTesting.Duopoly.payoffs_rival_no_test
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:31.988458+00:00
-- url     : https://prove2.me/theorems/4a1bb50b-4967-4603-80d0-6a52f4e5fd80
-- title:
--   Proof of Prop. 2, p. 36 — payoffs against a non-tester: the closed forms of Π^{1,0} and Π^{0,0}
-- statement:
--   Assume the standing assumptions $V,B,\rho>0$, $\delta\in(0,1]$, $\gamma,\theta\in(0,1)$, and suppose the rival does not test ($QA^{i'}=0$). Then a firm that tests earns
--   $$\Pi^{1,0}=\frac{VB(V+B)}{(3V+4B)^2}+\theta\cdot\frac{4(V+B)\gamma}{(3+\gamma)^2},$$
--   and a firm that does not test earns
--   $$\Pi^{0,0}=\theta(1-\theta)\cdot\frac{(V+B)(1-\gamma)\gamma}{(3+\gamma)^2}+(1-\theta)\theta\cdot\frac{4(V+B)\gamma}{(3+\gamma)^2}-\theta\rho.$$
--
--   The tester sells the mature product against the rival's innovation at $t=1$, and profits at $t=2$ only if the rival's product fails. Two non-testers earn nothing at $t=1$ (identical products), each pays the fixed recall cost $\rho$ with probability $\theta$ (its first-period profit being zero), and at $t=2$ earn a profit only when exactly one of the two products failed. These two payoffs determine the rival-does-not-test column of the testing game.
--
--   **Formalization Note** $\Pi^{a,b}$ is the model's payoff, built from the recall events and from demand-based period profits; the identity is not definitional.
-- source:
--   Kim, Koenigsberg & Ofek, I Don’t “Recall”, SSRN working paper 3492105 (Nov. 2019), p. 36 (PDF 37), proof of Proposition 2, case “Rival strategy is not to test”

import Mathlib
import Definitions.Def_RecallTesting_Duopoly_Model

namespace RecallTesting.Duopoly

theorem payoffs_rival_no_test (P : Params) (hS : P.Standing) :
    payoff P true false =
      P.V * P.B * (P.V + P.B) / (3 * P.V + 4 * P.B) ^ 2
        + P.θ * (4 * (P.V + P.B) * P.γ / (3 + P.γ) ^ 2) ∧
    payoff P false false =
      P.θ * (1 - P.θ) * ((P.V + P.B) * (1 - P.γ) * P.γ / (3 + P.γ) ^ 2)
        + (1 - P.θ) * P.θ * (4 * (P.V + P.B) * P.γ / (3 + P.γ) ^ 2) - P.θ * P.ρ := by sorry

end RecallTesting.Duopoly
