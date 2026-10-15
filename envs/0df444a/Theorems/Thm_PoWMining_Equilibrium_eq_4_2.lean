-- Prove2me | Theorems.Thm_PoWMining_Equilibrium_eq_4_2
-- name    : PoWMining.Equilibrium.eq_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:06.294269+00:00
-- url     : https://prove2.me/theorems/ef05d4b3-d1fb-4f28-91dc-22af9f0d76e8
-- title:
--   (4.2), p. 13 — first-order condition: for an active miner, $(R/H^*)(1-h^*_i/H^*)=c_i+\gamma h^*_i$
-- statement:
--   Consider the mining game with $N\ge 2$ miners, reward $R>0$, capacity parameter $\gamma\ge 0$ and sorted positive costs-per-hash $0<c_1\le\cdots\le c_N$ (payoff (3.4) without the fixed cost). Let $h^*$ be an equilibrium hash rate profile with aggregate $H^*=\sum_j h^*_j$, and let $i$ be an active miner, $h^*_i>0$. Then marginal gain equals marginal cost:
--   $$\frac{R}{H^*}\Bigl(1-\frac{h^*_i}{H^*}\Bigr)=c_i+\gamma h^*_i. \tag{4.2}$$
--
--   This is the first-order condition of miner $i$'s objective at an interior best response. Summing it over the active miners gives (B.1), and solving it for $h^*_i$ gives the hash rate formula of Proposition 4.1.
--
--   **Formalization Note** $H^*>0$ follows from $h^*_i>0$ and the nonnegativity of the profile, so the divisions are genuine.
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, p. 13, (4.2)

import Mathlib
import Definitions.Def_PoWMining_Equilibrium_Setting

namespace PoWMining.Equilibrium

/-- First-order condition (4.2), p. 13: for an active miner `i` in equilibrium,
`(R/H*)(1 − h*ᵢ/H*) = cᵢ + γ h*ᵢ`. -/
theorem eq_4_2 {N : ℕ} (P : Params N) (hP : P.Standing) (h : Fin N → ℝ)
    (hh : IsMiningEq P h) (i : Fin N) (hi : 0 < h i) :
    P.R / aggH h * (1 - h i / aggH h) = P.c i + P.γ * h i := by sorry

end PoWMining.Equilibrium
