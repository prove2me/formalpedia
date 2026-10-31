-- Prove2me | Theorems.Thm_PegProtect_Equilibrium_equation_3_3
-- name    : PegProtect.Equilibrium.equation_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:26.70834+00:00
-- url     : https://prove2.me/theorems/8f1effb4-304d-4f7a-af6c-dfd3f5822423
-- title:
--   (3.3), p. 16 — expected net surplus of a market order: π_m = ((ϕ − d)/(1 + ω)) ω + (ϕ − 1)/(1 + ω)
-- statement:
--   Under the standing market restrictions and for $0\le\omega<1$, the expected net surplus of a market order under the steady state $q$ has the closed form
--   $$\pi_m(\omega)=(\varphi-d)\sum_{k=-\infty}^{-1}q_k+(\varphi-1)\sum_{k=0}^{\infty}q_k=\frac{\varphi-d}{1+\omega}\,\omega+\frac{\varphi-1}{1+\omega}.$$
--
--   A market order executes against a resting contra-side peg at the midpoint and pays the fee $d$, and otherwise executes at the best bid or offer, one half-spread away from $V$. The closed form is the right-hand side of the indifference condition (3.9).
--
--   **Formalization Note** The algebraic identity uses only the tail sums of $q$, but the standing restrictions are retained because the source states the payoff in its baseline market model.
-- source:
--   Aldrich & Friedman, Order Protection through Delayed Messaging, SSRN 2999059 (version of March 3, 2019), p. 16, §3.3, (3.3)

import Mathlib
import Definitions.Def_PegProtect_Equilibrium_Model

namespace PegProtect.Equilibrium

theorem equation_3_3 (P : Params) (hP : P.Standing) (ω : ℝ) (h0 : 0 ≤ ω) (h1 : ω < 1) :
    piM P ω = (P.phi - P.d) / (1 + ω) * ω + (P.phi - 1) / (1 + ω) := by sorry

end PegProtect.Equilibrium
