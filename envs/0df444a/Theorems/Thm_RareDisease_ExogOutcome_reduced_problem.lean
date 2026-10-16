-- Prove2me | Theorems.Thm_RareDisease_ExogOutcome_reduced_problem
-- name    : RareDisease.ExogOutcome.reduced_problem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:13.328465+00:00
-- url     : https://prove2.me/theorems/c85a31f6-057f-4dcb-a1a7-f2aac5be3c3f
-- title:
--   (20), p. 15 — welfare p(1 − (1 − β)p)³/(4(1 − α)k) and spending at the manufacturer's best response
-- statement:
--   Consider Setting (2B) with $k>0$, $p\in(0,1)$ and a subsidy policy $(\alpha,\beta)\in[0,1)^2$. At every best response $e$ of the manufacturer, the patient welfare $W=\tfrac12 e(1-(1-\beta)p)^2$ and the government spending $M=\alpha k e^2+e\beta p[1-(1-\beta)p]$ equal
--   $$W = \frac{p\,(1-(1-\beta)p)^3}{4(1-\alpha)k}, \qquad M = \frac{\alpha p^2(1-(1-\beta)p)^2}{4(1-\alpha)^2k} + \frac{\beta p^2(1-(1-\beta)p)^2}{2(1-\alpha)k}.$$
--
--   These are the objective and the constraint of the government's reduced problem (20), obtained by substituting the follower's response into (10).
--
--   **Formalization Note** The statement is quantified over every element of the best-response set rather than over the closed form (19), so it ties (20) to the game. The page's constraint carries a stray closing parenthesis, which has no effect.
-- source:
--   Olsder, Martagan, Tang, Improving Access to Rare Disease Treatments: Optimal Subsidies, Pricing, and Payment, SSRN working paper 3481150 (version of 2019-11-13), p. 15, (20)

import Mathlib
import Definitions.Def_RareDisease_ExogOutcome_Setting

namespace RareDisease.ExogOutcome

/-- (20), p. 15: at the manufacturer's best response the patient welfare is
`p (1 - (1 - β) p)³ / (4 (1 - α) k)` and the government's spending is
`α p² (1 - (1 - β) p)² / (4 (1 - α)² k) + β p² (1 - (1 - β) p)² / (2 (1 - α) k)`. -/
theorem reduced_problem (k p α β : ℝ) (hk : 0 < k) (hp0 : 0 < p) (hp1 : p < 1)
    (hpol : RareDisease.Endogenous.IsPolicy α β) (e : ℝ) (he : e ∈ BR k p α β) :
    welfare p β e = p * (1 - (1 - β) * p) ^ 3 / (4 * (1 - α) * k) ∧
    spend k p α β e = α * p ^ 2 * (1 - (1 - β) * p) ^ 2 / (4 * (1 - α) ^ 2 * k)
      + β * p ^ 2 * (1 - (1 - β) * p) ^ 2 / (2 * (1 - α) * k) := by sorry

end RareDisease.ExogOutcome
