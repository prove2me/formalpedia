-- Prove2me | Theorems.Thm_PoWMining_Equilibrium_proposition_4_2
-- name    : PoWMining.Equilibrium.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:14.56076+00:00
-- url     : https://prove2.me/theorems/4b494df5-aa1d-4e5f-97bf-c6b1281f63f2
-- title:
--   Proposition 4.2, p. 13 — equilibrium marginal costs $MC^*_i=c_i+\gamma h^*_i$ increase in i; $MC^*_i<R/H^*\iff c_i<R/H^*\iff i\le n$
-- statement:
--   Consider the mining game with $N\ge 2$ miners, reward $R>0$, capacity parameter $\gamma\ge 0$ and sorted positive costs-per-hash $0<c_1\le\cdots\le c_N$ (payoff (3.4) without the fixed cost). Let $h^*$ be an equilibrium hash rate profile with aggregate $H^*$ and $n$ active miners, and let
--   $$MC^*_i:=c_i+\gamma h^*_i \tag{4.3}$$
--   be the marginal cost of miner $i$. Then:
--
--   1. $(MC^*_i)_{1\le i\le N}$ is an increasing sequence;
--   2. for every miner $i$,
--   $$MC^*_i<\frac{R}{H^*}\iff c_i<\frac{R}{H^*}\iff 1\le i\le n; \tag{4.4}$$
--   3. $(c_i/MC^*_i)_{1\le i\le N}$ is increasing and $(\gamma h^*_i/MC^*_i)_{1\le i\le N}$ is decreasing.
--
--   Thus a miner is active exactly when its cost-per-hash is below the reward-per-hash, and the capacity component of the marginal cost carries more weight for the larger (cheaper) miners.
--
--   **Formalization Note** "Increasing" and "decreasing" are meant weakly, as in the paper's footnote 12 (`Monotone`, `Antitone`). $n$ is the number of active miners of $h^*$. The paper's miner $i$ is Lean index $i-1$, so "$1\le i\le n$" is `i.val < n`.
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, p. 13, Proposition 4.2, (4.3)–(4.4)

import Mathlib
import Definitions.Def_PoWMining_Equilibrium_Setting

namespace PoWMining.Equilibrium

/-- Proposition 4.2, p. 13: in equilibrium the marginal costs `MC*ᵢ = cᵢ + γh*ᵢ` (4.3) form an
increasing sequence; `MC*ᵢ < R/H* ⟺ cᵢ < R/H* ⟺ 1 ≤ i ≤ n` (4.4); and `(cᵢ/MC*ᵢ)` is increasing,
`(γh*ᵢ/MC*ᵢ)` decreasing. Here `n` is the number of active miners. -/
theorem proposition_4_2 {N : ℕ} (P : Params N) (hP : P.Standing) (h : Fin N → ℝ)
    (hh : IsMiningEq P h) :
    Monotone (margCost P h) ∧
      (∀ i : Fin N,
        (margCost P h i < P.R / aggH h ↔ P.c i < P.R / aggH h) ∧
          (P.c i < P.R / aggH h ↔ i.val < activeCount h)) ∧
      Monotone (fun i => P.c i / margCost P h i) ∧
      Antitone (fun i => P.γ * h i / margCost P h i) := by sorry

end PoWMining.Equilibrium
