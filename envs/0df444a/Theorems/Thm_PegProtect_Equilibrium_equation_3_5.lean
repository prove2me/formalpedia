-- Prove2me | Theorems.Thm_PegProtect_Equilibrium_equation_3_5
-- name    : PegProtect.Equilibrium.equation_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:24.941417+00:00
-- url     : https://prove2.me/theorems/ac84cb05-96fc-4085-adca-593f7ad7b3d9
-- title:
--   (3.5), p. 16 — market-maker flow profit: π_r = 2(1 − ω)ρ/((1 + ω)N_r) − 2ν
-- statement:
--   Under the standing market restrictions, for $0\le\omega<1$ and a positive mass $N_r$ of market makers, the expected flow profit of a market maker who keeps both a bid and an offer at the best bid and offer is
--   $$\pi_r=\frac{2(1-\omega)\rho\sum_{k=0}^{\infty}q_k}{N_r}-2\nu=2\,\frac{(1-\omega)\rho}{(1+\omega)N_r}-2\nu .$$
--
--   Investor market orders reach each side at rate $(1-\omega)\rho$ and find no contra-side midpoint liquidity with probability $\sum_{k\ge0}q_k=1/(1+\omega)$; the loss to snipers occurs at rate $\nu$ on each side. Setting $\pi_r=0$ yields the equilibrium mass (3.7).
--
--   **Formalization Note** A positive maker mass keeps the per-maker payoff within its economic domain; Lean division assigns a junk value at $N_r=0$.
-- source:
--   Aldrich & Friedman, Order Protection through Delayed Messaging, SSRN 2999059 (version of March 3, 2019), p. 16, §3.4, (3.5)

import Mathlib
import Definitions.Def_PegProtect_Equilibrium_Model

namespace PegProtect.Equilibrium

theorem equation_3_5 (P : Params) (hP : P.Standing) (ω Nr : ℝ)
    (h0 : 0 ≤ ω) (h1 : ω < 1) (hNr : 0 < Nr) :
    piR P ω Nr = 2 * ((1 - ω) * P.ρ / ((1 + ω) * Nr)) - 2 * P.ν := by sorry

end PegProtect.Equilibrium
