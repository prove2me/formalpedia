-- Prove2me | Theorems.Thm_RobustAuction_ROM_proposition_3
-- name    : RobustAuction.ROM.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T19:33:28.655986+00:00
-- url     : https://prove2.me/theorems/3a237b9b-f9fa-40e0-b6cc-a71a56e3c98e
-- title:
--   Proposition 3, p. 1021 — ROM is incentive compatible
-- statement:
--   Let $\mathcal U$ be a set of $n\times m$ valuation matrices with nonnegative entries and let $B_1,\dots,B_n\ge 0$ be the budgets. Take any choice of optimal solutions of the problems (12), (13), (14) of Algorithm ROM.a and (16), (17) of Algorithm ROM.b. Let $a^{\mathbf v}$ and $p^{\mathbf v}$ be the resulting allocation (20) and payments (21). Then the mechanism satisfies the incentive compatibility constraints (8) of LP (5). That is, for every buyer $i$, every true valuation vector $\mathbf v\in\mathcal U$ and every report $\mathbf u_i$ with $(\mathbf u_i,\mathbf v_{-i})\in\mathcal U$,
--   $$\sum_{j\in\mathcal M}v_{ij}\,a^{(\mathbf u_i,\mathbf v_{-i})}_{ij}-p^{(\mathbf u_i,\mathbf v_{-i})}_i\le\sum_{j\in\mathcal M}v_{ij}\,a^{\mathbf v}_{ij}-p^{\mathbf v}_i .$$
--
--   Truthful bidding is therefore a best response for every buyer, among the reports that keep the bid vector inside the uncertainty set.
--
--   **Formalization Note** Nonnegative valuations and budgets are the model's standing assumptions, made explicit. The selections of optimal solutions in (16) and (17) at the two bid vectors $\mathbf v$ and $(\mathbf u_i,\mathbf v_{-i})$ are arbitrary and need not be related.
-- source:
--   Bandi, Bertsimas, Optimal Design for Multi-Item Auctions: A Robust Optimization Approach, Math. Oper. Res. 39(4):1012–1038 (2014), p. 1021 (PDF p. 11), Proposition 3 (Incentive Compatibility); constraint (8), p. 1017

import Mathlib
import Definitions.Def_RobustAuction_ROM_AuctionLP
import Definitions.Def_RobustAuction_ROM_Mechanism

namespace RobustAuction.ROM

/-- Proposition 3 (Incentive compatibility; Bandi–Bertsimas 2014, p. 1021): ROM's allocation
(20) and payments (21) satisfy (8), for every choice of optimal solutions of (12)–(14), (16),
(17). Valuations in `U` and budgets are nonnegative (standing assumptions of the model). -/
theorem proposition_3 {n m : ℕ} (U : Set (Fin n → Fin m → ℝ)) (B : Fin n → ℝ)
    (hU : ∀ u ∈ U, ∀ i j, 0 ≤ u i j) (hB : ∀ i, 0 ≤ B i)
    (d : ROMData n m) (hd : IsROM U B d) :
    IncentiveCompatible U (alloc U d) (pay U d) := by sorry

end RobustAuction.ROM
