-- Prove2me | Theorems.Thm_PegProtect_Equilibrium_zero_profit
-- name    : PegProtect.Equilibrium.zero_profit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:27.026353+00:00
-- url     : https://prove2.me/theorems/0a7395ff-2205-4c9d-a391-48bb4009fc9f
-- title:
--   Proof of Proposition 3.2, p. 18 — π_r = π_s = 0 with N_r, N_s ≥ 0 ⇔ N_r = (ρ/ν)(1−ω)/(1+ω), N_s = (2ρ/c)(1−ω)/(1+ω)
-- statement:
--   Under the standing restrictions ($c>0$, $0\le d<1$, $\varphi>1$, $\delta,\rho,\nu>0$) and for $0\le\omega<1$, the free-entry conditions for proprietary traders have exactly one solution: for real masses $N_r,N_s$,
--   $$\big(N_r\ge0,\ N_s\ge0,\ \pi_r=0,\ \pi_s=0\big)\iff\Big(N_r=\frac{\rho}{\nu}\,\frac{1-\omega}{1+\omega},\quad N_s=\frac{2\rho}{c}\,\frac{1-\omega}{1+\omega}\Big).$$
--
--   Applied at $\omega=\omega^*$ this gives the equilibrium masses (3.7) and (3.8).
--
--   **Formalization Note** $\pi_r$ and $\pi_s$ are the profits (3.5) and (3.4) as defined in the model file. A zero mass is excluded automatically: with Lean's $x/0=0$ it gives $\pi_r=-2\nu$ or $\pi_s=-c$, both nonzero.
-- source:
--   Aldrich & Friedman, Order Protection through Delayed Messaging, SSRN 2999059 (version of March 3, 2019), p. 18, proof of Proposition 3.2 ("apply the second market equilibrium condition π_r = π_s = 0 to Equations (3.5) and (3.4) and solve for N_r and N_s")

import Mathlib
import Definitions.Def_PegProtect_Equilibrium_Model

namespace PegProtect.Equilibrium

theorem zero_profit (P : Params) (hP : P.Standing) (ω Nr Ns : ℝ) (h0 : 0 ≤ ω) (h1 : ω < 1) :
    (0 ≤ Nr ∧ 0 ≤ Ns ∧ piR P ω Nr = 0 ∧ piS P Nr Ns = 0) ↔
      (Nr = P.ρ / P.ν * ((1 - ω) / (1 + ω)) ∧ Ns = 2 * P.ρ / P.c * ((1 - ω) / (1 + ω))) := by sorry

end PegProtect.Equilibrium
