-- Prove2me | Theorems.Thm_PoWMining_Investment_invested_cost_order
-- name    : PoWMining.Investment.invested_cost_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:45.702316+00:00
-- url     : https://prove2.me/theorems/e60cd538-7564-4976-8e5f-6c22b1718447
-- title:
--   p. 45, proof of Proposition 5.1 — for η > 0, investing min{1/η,1} preserves the strict order of costs
-- statement:
--   Under the standing assumptions of the investment model, suppose $\eta>0$ and every miner invests $\bar\beta=\min\{1/\eta,1\}$. Then, for all miners $i,j$,
--
--   $$
--   \tilde c_i<\tilde c_j\ \Longrightarrow\ c_i(\bar\beta)<c_j(\bar\beta).
--   $$
--
--   Since $c_i(\bar\beta)$ depends on $i$ only through $\tilde c_i$, equal initial costs stay equal, so the order of the miners by cost is the same before and after investment. The proof of Proposition 5.1 uses this to compare miners after investment.
--
--   **Formalization Note** The scope $\eta>0$ is the paper's: at $\eta=0$ every invested cost equals $\tilde c_0$ and the order collapses, as p. 45 notes ("in which case the cost of all miners becomes $\tilde c_0$").
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, p. 45, proof of Proposition 5.1

import Mathlib
import Definitions.Def_PoWMining_Investment_Model

namespace PoWMining.Investment

/-- Proof of Proposition 5.1, p. 45: for `η > 0`, if every miner invests `min{1/η, 1}`, the
strict order of the miners' costs-per-hash is preserved. -/
theorem invested_cost_order {N : ℕ} (P : InvParams N) (hP : P.Standing) (hη : 0 < P.η) :
    ∀ i j : Fin N, P.ct i < P.ct j →
      cost P (fun _ => betaBar P) i < cost P (fun _ => betaBar P) j := by sorry

end PoWMining.Investment
