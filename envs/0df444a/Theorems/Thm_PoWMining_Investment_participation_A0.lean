-- Prove2me | Theorems.Thm_PoWMining_Investment_participation_A0
-- name    : PoWMining.Investment.participation_A0
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:37.320616+00:00
-- url     : https://prove2.me/theorems/7830f589-71f2-4152-8879-934f6c9e8f39
-- title:
--   p. 45, proof of Proposition 5.1 — after the first |A(0)| miners invest, the Proposition 4.4 participation condition holds for miner |A(0)|
-- statement:
--   Consider the investment game under its standing assumptions, with $h^*$ any mining-equilibrium selection, and let $m=|A(0)|$ be the number of miners active without investment. Suppose miners $1,\dots,m$ invest $\min\{1/\eta,1\}$ and the others invest $0$ (the profile $\beta^{(m)}$), and write $c_j=c_j(\beta^{(m)}_j)$ and $c^{(m)}=c_1+\dots+c_m$. Then the participation condition of Proposition 4.4 holds for miner $m$:
--
--   $$
--   c_m<\frac{c^{(m)}+R\gamma/c_m}{m-1}.
--   $$
--
--   In the proof of Proposition 5.1 this is the step showing that the number of investing miners is at least $|A(0)|$: the miners active without investment remain active once they invest.
--
--   **Formalization Note** Miner $m$ is Lean index $m-1$; the statement quantifies over the Lean index $i$ with $i+1=m$. The inequality is in Proposition 4.4's printed division form. The paper's rewriting of it divides by $i-2$, which is $0$ when $|A(0)|=2$; the statement itself is posed for every $m$.
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, p. 45, proof of Proposition 5.1; p. 14, Proposition 4.4

import Mathlib
import Definitions.Def_PoWMining_Investment_Model

namespace PoWMining.Investment

/-- Proof of Proposition 5.1, p. 45: with `m = |A(0)|`, if the first `m` miners invest
`min{1/η, 1}` (profile `β^{(m)}`), the participation condition of Proposition 4.4 holds for the
`m`-th miner (Lean index `m - 1`) at the invested costs:
`c_m < (c^{(m)} + Rγ/c_m)/(m - 1)`. -/
theorem participation_A0 {N : ℕ} (P : InvParams N) (hP : P.Standing)
    (hstar : (Fin N → ℝ) → Fin N → ℝ) (hsel : IsSelection P hstar) :
    ∀ i : Fin N, i.val + 1 = (A0 hstar).card →
      partCond (cost P (betaK P (A0 hstar).card)) P.R P.γ (A0 hstar).card i := by sorry

end PoWMining.Investment
