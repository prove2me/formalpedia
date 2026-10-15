-- Prove2me | Theorems.Thm_PoWMining_Equilibrium_proposition_4_1
-- name    : PoWMining.Equilibrium.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:05.610666+00:00
-- url     : https://prove2.me/theorems/826d7d0c-dad7-48e6-a818-3850737e7d8a
-- title:
--   Proposition 4.1, p. 12 — the mining game has a unique equilibrium; the n cheapest miners are active, with explicit $h^*_i$ and $H^*$
-- statement:
--   Consider the mining game with $N\ge 2$ miners, reward $R>0$, capacity parameter $\gamma\ge 0$ and sorted positive costs-per-hash $0<c_1\le\cdots\le c_N$, in which miner $i$ choosing $h_i\ge 0$ earns $(h_i/H)R-c_ih_i-(\gamma/2)h_i^2$ if $H=\sum_jh_j>0$ and $0$ if $H=0$.
--
--   1. There exists a unique equilibrium hash rate profile $h^*$.
--   2. For the equilibrium $h^*$ there is some $2\le n\le N$ such that, with $H^*=\sum_j h^*_j$,
--   $$h^*_i=\begin{cases}\dfrac{H^*(R-c_iH^*)}{R+\gamma(H^*)^2}, & 1\le i\le n,\\[4pt] 0, & n<i\le N,\end{cases}$$
--   and
--   $$H^*=\begin{cases}\dfrac{\sqrt{(c^{(n)})^2+4(n-1)R\gamma}-c^{(n)}}{2\gamma}, & \gamma>0,\\[6pt] \dfrac{(n-1)R}{c^{(n)}}, & \gamma=0,\end{cases}\tag{4.1}$$
--   where $c^{(n)}=c_1+\cdots+c_n$.
--
--   This is the basic structural result of the mining stage: the equilibrium is unique, the active miners are the $n$ cheapest ones, and all hash rates are explicit once $n$ is known. Proposition 4.4 then identifies $n$ from the parameters.
--
--   **Formalization Note** The paper states the result "for any $\beta\in[0,1]^N$"; with the investment profile fixed, the costs-per-hash are an arbitrary sorted positive vector, which is how it is stated here. The paper's miner $i$ is Lean index $i-1$, so "$1\le i\le n$" is `i.val < n`. The equation $H^*=\dots$ selects the first branch when $\gamma>0$ and the second when $\gamma=0$.
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, p. 12, Proposition 4.1, (4.1)

import Mathlib
import Definitions.Def_PoWMining_Equilibrium_Setting

namespace PoWMining.Equilibrium

/-- Proposition 4.1, p. 12: there is a unique equilibrium hash rate profile `h*`; for some
`2 ≤ n ≤ N`, `h*ᵢ = H*(R − cᵢH*)/(R + γ(H*)²)` for the first `n` miners and `0` for the others,
and `H*` is given by (4.1). -/
theorem proposition_4_1 {N : ℕ} (P : Params N) (hP : P.Standing) :
    (∃! h : Fin N → ℝ, IsMiningEq P h) ∧
      ∀ h : Fin N → ℝ, IsMiningEq P h →
        ∃ n : ℕ, 2 ≤ n ∧ n ≤ N ∧ aggH h = aggForm P n ∧
          ∀ i : Fin N, h i =
            if i.val < n then aggH h * (P.R - P.c i * aggH h) / (P.R + P.γ * aggH h ^ 2) else 0 := by sorry

end PoWMining.Equilibrium
