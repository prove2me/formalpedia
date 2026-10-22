-- Prove2me | Theorems.Thm_TradingPostNSW_Leontief_pne_bid_eq_fee_off_tight
-- name    : TradingPostNSW.Leontief.pne_bid_eq_fee_off_tight
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:20.336299+00:00
-- url     : https://prove2.me/theorems/6fcad363-d58e-4cca-ba54-82c6de54e85c
-- title:
--   Proof of Theorem 4.7, p. 15 — at a PNE of TP(∆) an agent bids exactly ∆ on its demanded goods outside the tight set S_i
-- statement:
--   Consider an instance satisfying the standing assumptions and perfect competition, an entrance fee $0 < \Delta < 1/m$, and a pure Nash equilibrium $b$ of $\mathcal{TP}(\Delta)$ with induced allocation $x$. For agent $i$ and $j \in D_i$ let $\phi_{i,j} = x_{i,j}/v_{i,j}$, so that $u_i(x_i) = \min_{j \in D_i} \phi_{i,j}$, and let $S_i = \{ j \in D_i \mid \phi_{i,j} = u_i(x_i)\}$ be the tight set. Then
--   $$b_{i,j} = \Delta \qquad \text{for every } j \in D_i \setminus S_i.$$
--
--   An agent receiving more than it needs of a good would shift money from it to its tight goods; at an equilibrium only the entrance fee is left on such goods. This bounds the money spent outside the tight set, the key quantity in the proof of Theorem 4.7.
--
--   **Formalization Note** The page writes $\phi_{i,j}$ with the nominal bids $\tilde b$; it is encoded with the induced allocation, the same number at an equilibrium since every bid is $0$ or at least $\Delta$. The page's "$S_i = M$" and "$j \in M \setminus S_i$" refer to $D_i$.
-- source:
--   Brânzei, Gkatzelis, Mehta, Nash Social Welfare Approximation for Strategic Agents, arXiv:1607.01569v3, p. 15, proof of Theorem 4.7

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting

namespace TradingPostNSW.Leontief

/-- Proof of Theorem 4.7, p. 15: at a pure Nash equilibrium of `TP(Δ)`, agent `i` bids exactly
`Δ` on every demanded good outside its tight set `S_i`. -/
theorem pne_bid_eq_fee_off_tight {n m : ℕ} (I : Instance n m) (Δ : ℝ) (b : Fin n → Fin m → ℝ)
    (hI : Standing I) (hPC : PerfectCompetition I) (hΔ : 0 < Δ) (hΔm : Δ < 1 / (m : ℝ))
    (hb : IsPNE I Δ b) :
    ∀ i, ∀ j ∈ D I i \ tight I Δ b i, b i j = Δ := by sorry

end TradingPostNSW.Leontief
