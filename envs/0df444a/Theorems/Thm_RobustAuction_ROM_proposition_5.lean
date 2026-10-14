-- Prove2me | Theorems.Thm_RobustAuction_ROM_proposition_5
-- name    : RobustAuction.ROM.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T19:33:23.853988+00:00
-- url     : https://prove2.me/theorems/43ec37d0-f603-422c-a809-5213a50dae74
-- title:
--   Proposition 5, p. 1023 — ROM is individually rational
-- statement:
--   Let $\mathcal U$ be a set of $n\times m$ valuation matrices with nonnegative entries and let $B_1,\dots,B_n\ge 0$ be the budgets. Take any choice of optimal solutions of the problems (12), (13), (14) of Algorithm ROM.a and (16), (17) of Algorithm ROM.b. Let $a^{\mathbf v}$ and $p^{\mathbf v}$ be the resulting allocation (20) and payments (21). Then the mechanism satisfies the individual rationality constraints (10) of LP (5):
--   $$p^{\mathbf v}_i\le\sum_{j\in\mathcal M}v_{ij}\,a^{\mathbf v}_{ij}\qquad\text{for all } i\in\mathcal N \text{ and all } \mathbf v\in\mathcal U .$$
--
--   A buyer who bids truthfully never derives negative utility from participating.
--
--   **Formalization Note** Nonnegative valuations and budgets are the model's standing assumptions, made explicit. The paper's proof uses them in its last step ("$x^*_{kj}$, $\theta^*_k$, and $\tilde u_{kj}$ are all nonnegative"). The printed title reads "Individually Rationality".
-- source:
--   Bandi, Bertsimas, Optimal Design for Multi-Item Auctions: A Robust Optimization Approach, Math. Oper. Res. 39(4):1012–1038 (2014), p. 1023 (PDF p. 13), Proposition 5 (Individually Rationality); constraint (10), p. 1017

import Mathlib
import Definitions.Def_RobustAuction_ROM_AuctionLP
import Definitions.Def_RobustAuction_ROM_Mechanism

namespace RobustAuction.ROM

/-- Proposition 5 (Individual rationality; Bandi–Bertsimas 2014, p. 1023): ROM's allocation
(20) and payments (21) satisfy (10), for every choice of optimal solutions of (12)–(14), (16),
(17). Valuations in `U` and budgets are nonnegative (standing assumptions of the model). -/
theorem proposition_5 {n m : ℕ} (U : Set (Fin n → Fin m → ℝ)) (B : Fin n → ℝ)
    (hU : ∀ u ∈ U, ∀ i j, 0 ≤ u i j) (hB : ∀ i, 0 ≤ B i)
    (d : ROMData n m) (hd : IsROM U B d) :
    IndividuallyRational U (alloc U d) (pay U d) := by sorry

end RobustAuction.ROM
