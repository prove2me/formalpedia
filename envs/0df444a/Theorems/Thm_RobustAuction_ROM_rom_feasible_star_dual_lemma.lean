-- Prove2me | Theorems.Thm_RobustAuction_ROM_rom_feasible_star_dual_lemma
-- name    : RobustAuction.ROM.rom_feasible_star_dual_lemma
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-21T16:04:47.610762+00:00
-- url     : https://prove2.me/theorems/b4eeeaab-8195-4b3a-bef5-e5e8e06393c4
-- title:
--   ROM dual lemma (star): the reservation-price budget inequality
-- statement:
--   Let $\mathcal U$ be a set of $n\times m$ valuation matrices with nonnegative entries and let $B_1,\dots,B_n\ge 0$ be the budgets. Let $d$ be any choice of optimal solutions of the problems (12), (14) and (13) of Algorithm ROM.a (i.e. `IsROMa U B d`: $z\in\mathcal U$, $x^*$ inner-feasible at $z$ with maximal inner value, the (14) minimizers $\tilde u^i\in\mathcal U$, and the dual-feasible optimal $(\xi^*,\eta^*,\theta^*)$ of (13)). With the reservation prices $r^*_{ij}=\xi^*_j+z_{ij}\eta^*_i+z_{ij}\theta^*_i$ of (15), for every buyer $i$:
--
--   $$\sum_j x^*_{ij}\,r^*_{ij}\le B_i+\theta^*_i\sum_j x^*_{ij}\,\tilde u^i_j.$$
--   This is the key dual-lemma step in Bandi-Bertsimas (2014), Optimal Design for Multi-Item Auctions, proof of Proposition 3: it feeds the budget-feasibility constraint (9) of the feasibility of ROM's allocation and payments. It follows from the formalized hypotheses by LP complementary slackness on the primal-dual pair of (13): both $z$ and $\tilde u^i$ minimize $u\mapsto\sum_j x^*_{ij}u_{ij}$ over $\mathcal U$ (so $\sum_j x^*_{ij}\tilde u^i_j=\sum_j x^*_{ij}z_{ij}$), $x^*$ is primal-optimal, and complementary slackness gives $x^*_{ij}(r^*_{ij}-z_{ij})=0$ for all $i,j$; the inequality then collapses to $(1-\theta^*_i)T_i\le T_i\le B_i$ with $T_i=\sum_j x^*_{ij}\tilde u^i_j$.
-- source:
--   Bandi, Bertsimas, Optimal Design for Multi-Item Auctions: A Robust Optimization Approach, Math. Oper. Res. 39(4):1012-1038 (2014), step in the proof of Proposition 3, pp. 1021-1022 (the (star) inequality feeding budget-feasibility (9) of ROM); formalized corollary of RobustAuction.ROM.rom_feasible's hypotheses (IsROMa + hU + hB); TERMINAL_VERDICT_A triage 2026-10-20

import Mathlib
import Definitions.Def_RobustAuction_ROM_AuctionLP
import Definitions.Def_RobustAuction_ROM_Mechanism

namespace RobustAuction.ROM

/-- The (star) dual lemma for ROM (Bandi-Bertsimas 2014, step in the proof of
Proposition 3, used for the budget-feasibility half (9) of the feasibility of ROM):
for every buyer `i`,
`sum_j x*_ij * r*_ij <= B_i + theta*_i * sum_j x*_ij * utilde^i_j`,
where `r*_ij = xi*_j + z_ij * eta*_i + z_ij * theta*_i` are the reservation prices (15)
and `utilde^i_j = ut i i j` is the (14) minimizer. It is a corollary of the
formalized hypotheses `IsROMa` (dual feasibility and optimality of (13), (12)'s
inner-feasibility at `z`, and the (14) minimizers) plus nonnegativity of `U` and `B`,
via LP complementary slackness on the primal-dual pair of (13). -/
theorem rom_feasible_star_dual_lemma {n m : ℕ} (U : Set (Fin n → Fin m → ℝ))
    (B : Fin n → ℝ)
    (hU : ∀ u ∈ U, ∀ i j, 0 ≤ u i j) (hB : ∀ i, 0 ≤ B i)
    (d : ROMData n m) (hROMa : IsROMa U B d) :
    ∀ i, Finset.sum Finset.univ (fun j => d.xs i j * rStar d i j) ≤
      B i + d.θ i * Finset.sum Finset.univ (fun j => d.xs i j * d.ut i i j) := by
  sorry

end RobustAuction.ROM
