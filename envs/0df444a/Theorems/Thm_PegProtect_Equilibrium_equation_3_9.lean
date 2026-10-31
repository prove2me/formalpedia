-- Prove2me | Theorems.Thm_PegProtect_Equilibrium_equation_3_9
-- name    : PegProtect.Equilibrium.equation_3_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:28.953103+00:00
-- url     : https://prove2.me/theorems/3eb3fe96-b2cd-4acd-9b68-c3cbfe686437
-- title:
--   (3.9), proof of Proposition 3.2, p. 18 — π_p = π_m ⇔ ω = (ϕ − d − β⁻¹(ϕ − 1))/(1 − d)
-- statement:
--   Under the standing restrictions ($c>0$, $0\le d<1$, $\varphi>1$, $\delta,\rho,\nu>0$, $\beta=e^{-\delta/\rho}$) and for $0\le\omega<1$, a midpoint peg order and a market order have the same expected net surplus exactly at one value of $\omega$:
--   $$\pi_p(\omega)=\pi_m(\omega)\iff\omega=\frac{\varphi-d-\beta^{-1}(\varphi-1)}{1-d}.$$
--
--   This is the indifference condition behind the first equilibrium condition of Definition 3.1, and it produces the interior branch of (3.6).
--
--   **Formalization Note** The payoffs $\pi_p,\pi_m$ are the defining sums of (3.2) and (3.3), not their closed forms.
-- source:
--   Aldrich & Friedman, Order Protection through Delayed Messaging, SSRN 2999059 (version of March 3, 2019), p. 18, proof of Proposition 3.2, (3.9)

import Mathlib
import Definitions.Def_PegProtect_Equilibrium_Model

namespace PegProtect.Equilibrium

theorem equation_3_9 (P : Params) (hP : P.Standing) (ω : ℝ) (h0 : 0 ≤ ω) (h1 : ω < 1) :
    piP P ω = piM P ω ↔ ω = (P.phi - P.d - P.beta⁻¹ * (P.phi - 1)) / (1 - P.d) := by sorry

end PegProtect.Equilibrium
