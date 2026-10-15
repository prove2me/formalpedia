-- Prove2me | Theorems.Thm_PoWMining_Equilibrium_eq_B_1
-- name    : PoWMining.Equilibrium.eq_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:16.610965+00:00
-- url     : https://prove2.me/theorems/4c0a43d7-74d4-46ca-91dd-e018e9a89227
-- title:
--   (B.1), p. 38 — summing the first-order conditions: $0=\frac{n-1}{H}R-c^{(n)}-\gamma H=\frac1H((n-1)R-c^{(n)}H-\gamma H^2)$
-- statement:
--   Consider the mining game with $N\ge 2$ miners, reward $R>0$, capacity parameter $\gamma\ge 0$ and sorted positive costs-per-hash $0<c_1\le\cdots\le c_N$ (payoff (3.4) without the fixed cost). Let $h^*$ be an equilibrium hash rate profile, $H=\sum_j h^*_j$ its aggregate, $n=|\{i:h^*_i>0\}|$ its number of active miners, and $c^{(n)}=c_1+\cdots+c_n$ the cumulative cost of the first $n$ miners. Then $H>0$ and
--   $$0=\frac{n-1}{H}R-c^{(n)}-\gamma H=\frac{1}{H}\bigl((n-1)R-c^{(n)}H-\gamma H^2\bigr). \tag{B.1}$$
--
--   So the aggregate hash rate is the positive root of the quadratic $\gamma H^2+c^{(n)}H-(n-1)R=0$, which is the closed form (4.1).
--
--   **Formalization Note** The statement uses the cumulative cost of the first $n$ miners in the paper's order (Lean indices $<n$); that these are exactly the active miners is the content of the preceding milestone. The paper's miner $i$ is Lean index $i-1$.
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, p. 38, proof of Proposition 4.1, (B.1)

import Mathlib
import Definitions.Def_PoWMining_Equilibrium_Setting

namespace PoWMining.Equilibrium

/-- (B.1), p. 38: summing the first-order conditions of the `n` active miners,
`0 = ((n − 1)/H) R − c⁽ⁿ⁾ − γ H = (1/H)((n − 1) R − c⁽ⁿ⁾ H − γ H²)`, with `H = H* > 0`. -/
theorem eq_B_1 {N : ℕ} (P : Params N) (hP : P.Standing) (h : Fin N → ℝ)
    (hh : IsMiningEq P h) :
    0 < aggH h ∧
      ((activeCount h : ℝ) - 1) / aggH h * P.R - cumCost P (activeCount h) - P.γ * aggH h = 0 ∧
      1 / aggH h * (((activeCount h : ℝ) - 1) * P.R - cumCost P (activeCount h) * aggH h
        - P.γ * aggH h ^ 2) = 0 := by sorry

end PoWMining.Equilibrium
