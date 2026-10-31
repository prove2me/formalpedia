-- Prove2me | Theorems.Thm_PegProtect_Equilibrium_boundary
-- name    : PegProtect.Equilibrium.boundary
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:25.100763+00:00
-- url     : https://prove2.me/theorems/663fac3c-4550-440a-a973-8c6f78f3dc44
-- title:
--   Proof of Proposition 3.2, p. 18 — the root ω̂ of (3.9) is < 1, and ω̂ ≤ 0 implies π_p(0) ≤ π_m(0)
-- statement:
--   Under the standing restrictions ($c>0$, $0\le d<1$, $\varphi>1$, $\delta,\rho,\nu>0$, $\beta=e^{-\delta/\rho}$), let
--   $$\hat\omega=\frac{\varphi-d-\beta^{-1}(\varphi-1)}{1-d}$$
--   be the last expression of (3.9). Then
--   1. $\hat\omega<1$;
--   2. if $\hat\omega\le0$, then $\pi_p(0)\le\pi_m(0)$: when no investor uses pegs, a peg order earns no more than a market order.
--
--   These are the two boundary claims of the proof of Proposition 3.2: the first rules out $\omega^*=1$, the second makes $\omega^*=0$ an equilibrium share when the root is not positive.
--
--   **Formalization Note** The paper states the second claim for a negative root; at $\hat\omega=0$ it holds with equality, so it is stated for $\hat\omega\le0$. The first claim uses $\varphi>1$ and $\beta<1$.
-- source:
--   Aldrich & Friedman, Order Protection through Delayed Messaging, SSRN 2999059 (version of March 3, 2019), p. 18, proof of Proposition 3.2, paragraph after (3.9)

import Mathlib
import Definitions.Def_PegProtect_Equilibrium_Model

namespace PegProtect.Equilibrium

theorem boundary (P : Params) (hP : P.Standing) :
    omegaHat P < 1 ∧ (omegaHat P ≤ 0 → piP P 0 ≤ piM P 0) := by sorry

end PegProtect.Equilibrium
