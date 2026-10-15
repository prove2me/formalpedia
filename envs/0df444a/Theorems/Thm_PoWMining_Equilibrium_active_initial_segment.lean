-- Prove2me | Theorems.Thm_PoWMining_Equilibrium_active_initial_segment
-- name    : PoWMining.Equilibrium.active_initial_segment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:07.791008+00:00
-- url     : https://prove2.me/theorems/11f285f3-a06b-4766-be4b-496f3d8507c4
-- title:
--   p. 38, proof of Proposition 4.1 — if miner k + 1 is active in equilibrium, so is miner k: the active miners are the cheapest ones
-- statement:
--   Consider the mining game with $N\ge 2$ miners, reward $R>0$, capacity parameter $\gamma\ge 0$ and sorted positive costs-per-hash $0<c_1\le\cdots\le c_N$ (payoff (3.4) without the fixed cost). Let $h^*$ be an equilibrium hash rate profile. Then for all miners $i\le j$,
--   $$h^*_j>0\ \Longrightarrow\ h^*_i>0.$$
--   Equivalently, the active set is an initial segment $\{1,\dots,n\}$ of the miners ordered by cost.
--
--   The paper proves the step from miner $k+1$ to miner $k$: an inactive miner $k$ would face a marginal gain $R/H$ strictly larger than the marginal cost of the active miner $k+1$, which is at least $c_{k+1}\ge c_k$. Iterating the step gives the statement above. Together with the existence of at least two active miners, it reduces the equilibrium to a choice of the number $n$ of active miners.
--
--   **Formalization Note** Miners are indexed by `Fin N`; the paper's miner $i$ is Lean index $i-1$, and the order on indices is the paper's order.
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, p. 38, proof of Proposition 4.1 (display MG_k > … > MC_k)

import Mathlib
import Definitions.Def_PoWMining_Equilibrium_Setting

namespace PoWMining.Equilibrium

/-- Proof of Proposition 4.1, p. 38: if miner `k + 1` is active in equilibrium, then miner `k`
is active; hence (miners sorted by cost) every miner cheaper-indexed than an active miner is active. -/
theorem active_initial_segment {N : ℕ} (P : Params N) (hP : P.Standing) (h : Fin N → ℝ)
    (hh : IsMiningEq P h) (i j : Fin N) (hij : i ≤ j) (hj : 0 < h j) : 0 < h i := by sorry

end PoWMining.Equilibrium
