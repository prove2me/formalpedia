-- Prove2me | Theorems.Thm_RecallTesting_Duopoly_payoffs_rival_tests
-- name    : RecallTesting.Duopoly.payoffs_rival_tests
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:45.898273+00:00
-- url     : https://prove2.me/theorems/271fc292-6b20-4811-892d-70519686435e
-- title:
--   Proof of Prop. 2, p. 36 — payoffs against a tester: Π^{1,1} = 0 and the closed form of Π^{0,1}
-- statement:
--   Assume the standing assumptions $V,B,\rho>0$, $\delta\in(0,1]$, $\gamma,\theta\in(0,1)$, and suppose the rival tests ($QA^{i'}=1$). Then a firm that also tests earns
--   $$\Pi^{1,1}=0,$$
--   and a firm that does not test earns
--   $$\Pi^{0,1}=\frac{4B(V+B)^2}{(3V+4B)^2}+\theta\left(-\delta\cdot\frac{4B(V+B)^2}{(3V+4B)^2}-\rho+\frac{(V+B)(1-\gamma)\gamma}{(3+\gamma)^2}\right).$$
--
--   The non-tester earns the innovation's profit against the mature product at $t=1$; with probability $\theta$ its product fails, it pays $\rho+\delta\pi_1$ and sells a recalled innovation against the rival's innovation at $t=2$; otherwise the two innovations are identical at $t=2$. These two payoffs determine the rival-tests column of the testing game.
--
--   **Formalization Note** $\Pi^{a,b}$ is the model's payoff, built from the recall events and from demand-based period profits; the identity is not definitional.
-- source:
--   Kim, Koenigsberg & Ofek, I Don’t “Recall”, SSRN working paper 3492105 (Nov. 2019), p. 36 (PDF 37), proof of Proposition 2, case “Rival strategy is to test”

import Mathlib
import Definitions.Def_RecallTesting_Duopoly_Model

namespace RecallTesting.Duopoly

theorem payoffs_rival_tests (P : Params) (hS : P.Standing) :
    payoff P true true = 0 ∧
    payoff P false true =
      4 * P.B * (P.V + P.B) ^ 2 / (3 * P.V + 4 * P.B) ^ 2
        + P.θ * (-P.δ * (4 * P.B * (P.V + P.B) ^ 2 / (3 * P.V + 4 * P.B) ^ 2) - P.ρ
          + (P.V + P.B) * (1 - P.γ) * P.γ / (3 + P.γ) ^ 2) := by sorry

end RecallTesting.Duopoly
