-- Prove2me | Theorems.Thm_PoWMining_Equilibrium_at_least_two_active
-- name    : PoWMining.Equilibrium.at_least_two_active
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:02.656557+00:00
-- url     : https://prove2.me/theorems/150d8a90-0f1a-437d-8bd4-c15e4070b66d
-- title:
--   p. 38, proof of Proposition 4.1 — every equilibrium has at least two active miners
-- statement:
--   Consider the mining game with $N\ge 2$ miners, reward $R>0$, capacity parameter $\gamma\ge 0$ and sorted positive costs-per-hash $0<c_1\le\cdots\le c_N$, where miner $i$ choosing hash rate $h_i\ge 0$ earns $\pi_i=(h_i/H)R-c_ih_i-(\gamma/2)h_i^2$ when the aggregate hash rate $H=\sum_j h_j$ is positive and $0$ when $H=0$.
--
--   Every equilibrium hash rate profile $h^*$ has at least two active miners:
--   $$\bigl|\{i : h^*_i>0\}\bigr|\ge 2.$$
--
--   If no miner were active, any miner could earn a positive profit by a small positive hash rate; if only one miner were active, it would win the whole reward at any positive hash rate and could gain by lowering it. This fact starts the uniqueness argument of Proposition 4.1.
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, p. 38, proof of Proposition 4.1

import Mathlib
import Definitions.Def_PoWMining_Equilibrium_Setting

namespace PoWMining.Equilibrium

/-- Proof of Proposition 4.1, p. 38: every equilibrium hash rate profile has at least two
active miners. -/
theorem at_least_two_active {N : ℕ} (P : Params N) (hP : P.Standing) (h : Fin N → ℝ)
    (hh : IsMiningEq P h) : 2 ≤ activeCount h := by sorry

end PoWMining.Equilibrium
