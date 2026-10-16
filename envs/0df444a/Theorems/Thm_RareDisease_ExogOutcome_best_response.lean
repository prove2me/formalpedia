-- Prove2me | Theorems.Thm_RareDisease_ExogOutcome_best_response
-- name    : RareDisease.ExogOutcome.best_response
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:06.538877+00:00
-- url     : https://prove2.me/theorems/b5599708-bf3d-4a71-a0f2-ac7acb2c0166
-- title:
--   (19), p. 15 — the manufacturer's unique best response is e* = p(1 − (1 − β)p)/(2(1 − α)k)
-- statement:
--   Consider Setting (2B) with R&D cost scale $k>0$ and consortium price $p\in(0,1)$. For every subsidy policy $(\alpha,\beta)\in[0,1)^2$, the manufacturer's profit $e\,p\,[1-(1-\beta)p]-(1-\alpha)ke^2$ has exactly one maximizer over $e>0$, namely
--   $$e^* = \frac{p\,(1-(1-\beta)p)}{2(1-\alpha)k}.$$
--
--   This is the follower's response in the Stackelberg game; every statement about the government's problem evaluates welfare and spending at this efficacy.
--
--   **Formalization Note** The best-response set is the set of maximizers over $e>0$, and the theorem says it equals the singleton $\{e^*\}$, i.e. both existence and uniqueness. The hypotheses $k>0$ and $0<p<1$ are the paper's standing assumptions made explicit: with $p\ge1$ and $\beta=0$ the bracket $1-(1-\beta)p$ is not positive and no maximizer with $e>0$ exists. The page says "Equation (10)"; the manufacturer's objective is (9).
-- source:
--   Olsder, Martagan, Tang, Improving Access to Rare Disease Treatments: Optimal Subsidies, Pricing, and Payment, SSRN working paper 3481150 (version of 2019-11-13), p. 15, (19)

import Mathlib
import Definitions.Def_RareDisease_ExogOutcome_Setting

namespace RareDisease.ExogOutcome

/-- (19), p. 15: in Setting (2B) the manufacturer's best response is unique and equals
`e* = p (1 - (1 - β) p) / (2 (1 - α) k)`. -/
theorem best_response (k p α β : ℝ) (hk : 0 < k) (hp0 : 0 < p) (hp1 : p < 1)
    (hpol : RareDisease.Endogenous.IsPolicy α β) :
    BR k p α β = {p * (1 - (1 - β) * p) / (2 * (1 - α) * k)} := by sorry

end RareDisease.ExogOutcome
