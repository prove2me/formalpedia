-- Prove2me | Theorems.Thm_RobustAuction_ROM_proposition_4
-- name    : RobustAuction.ROM.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T19:33:32.702967+00:00
-- url     : https://prove2.me/theorems/a93cec19-e5e1-4bfb-ac31-c41d84aa2bb6
-- title:
--   Proposition 4, p. 1022 — ROM is budget feasible
-- statement:
--   Let $\mathcal U$ be a set of $n\times m$ valuation matrices with nonnegative entries and let $B_1,\dots,B_n\ge 0$ be the budgets. Take any choice of optimal solutions of the problems (12), (13), (14) of Algorithm ROM.a and (16), (17) of Algorithm ROM.b, and let $p^{\mathbf v}$ be the resulting payments (21). Then the mechanism satisfies the budget constraints (9) of LP (5):
--   $$p^{\mathbf v}_i\le B_i\qquad\text{for all } i\in\mathcal N \text{ and all } \mathbf v\in\mathcal U .$$
--
--   No buyer is ever charged more than their budget when the bids lie in the uncertainty set.
--
--   **Formalization Note** Nonnegative valuations and budgets are the model's standing assumptions, made explicit; the paper's proof uses them, for instance to show that the padding of $\mathbf y^{\mathbf v-k}$ with a zero row lies in $\mathcal P$. Payments may be negative, and no lower bound on them is asserted.
-- source:
--   Bandi, Bertsimas, Optimal Design for Multi-Item Auctions: A Robust Optimization Approach, Math. Oper. Res. 39(4):1012–1038 (2014), p. 1022 (PDF p. 12), Proposition 4 (Budget Feasibility); constraint (9), p. 1017

import Mathlib
import Definitions.Def_RobustAuction_ROM_AuctionLP
import Definitions.Def_RobustAuction_ROM_Mechanism

namespace RobustAuction.ROM

/-- Proposition 4 (Budget feasibility; Bandi–Bertsimas 2014, p. 1022): ROM's payments (21)
satisfy (9), for every choice of optimal solutions of (12)–(14), (16), (17). Valuations in `U`
and budgets are nonnegative (standing assumptions of the model). -/
theorem proposition_4 {n m : ℕ} (U : Set (Fin n → Fin m → ℝ)) (B : Fin n → ℝ)
    (hU : ∀ u ∈ U, ∀ i j, 0 ≤ u i j) (hB : ∀ i, 0 ≤ B i)
    (d : ROMData n m) (hd : IsROM U B d) :
    BudgetFeasible U B (pay U d) := by sorry

end RobustAuction.ROM
