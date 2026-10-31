-- Prove2me | Theorems.Thm_PegProtect_Equilibrium_equation_3_2
-- name    : PegProtect.Equilibrium.equation_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:19.259493+00:00
-- url     : https://prove2.me/theorems/8640bf00-5d08-43c5-8c4b-7cdb20f6c685
-- title:
--   (3.2), p. 15 — expected net surplus of a midpoint peg: π_p = ((ϕ − d)/(1 + ω)) [ω + β(1 − ω)/(1 − βω)]
-- statement:
--   Under the standing restrictions ($c>0$, $0\le d<1$, $\varphi>1$, $\delta,\rho,\nu>0$, so that $\beta=e^{-\delta/\rho}\in(0,1)$) and for $0\le\omega<1$, the expected net surplus of a midpoint peg order under the steady state $q$ has the closed form
--   $$\pi_p(\omega)=(\varphi-d)\Big[\sum_{k=-\infty}^{-1}q_k+\sum_{k=0}^{\infty}q_k\beta^{k+1}\Big]=\frac{\varphi-d}{1+\omega}\Big[\omega+\frac{\beta(1-\omega)}{1-\beta\omega}\Big].$$
--
--   A peg executes at once against a resting contra-side peg, and otherwise waits behind $k$ same-side pegs and is discounted by $\beta^{k+1}$. The closed form is the left-hand side of the indifference condition (3.9).
--
--   **Formalization Note** The page writes this display for $\omega\in(0,1)$; it is stated for $0\le\omega<1$ so that the corner $\omega=0$ of Definition 3.1 is covered.
-- source:
--   Aldrich & Friedman, Order Protection through Delayed Messaging, SSRN 2999059 (version of March 3, 2019), p. 15, §3.3, (3.2)

import Mathlib
import Definitions.Def_PegProtect_Equilibrium_Model

namespace PegProtect.Equilibrium

theorem equation_3_2 (P : Params) (hP : P.Standing) (ω : ℝ) (h0 : 0 ≤ ω) (h1 : ω < 1) :
    piP P ω = (P.phi - P.d) / (1 + ω) * (ω + P.beta * (1 - ω) / (1 - P.beta * ω)) := by sorry

end PegProtect.Equilibrium
