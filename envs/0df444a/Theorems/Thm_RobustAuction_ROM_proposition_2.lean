-- Prove2me | Theorems.Thm_RobustAuction_ROM_proposition_2
-- name    : RobustAuction.ROM.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T19:33:23.525383+00:00
-- url     : https://prove2.me/theorems/c35ccff2-b64f-4518-b866-d93fbf488dae
-- title:
--   Proposition 2, p. 1020 — relations (22)–(27) among the quantities computed by ROM.a
-- statement:
--   Let $\mathcal U$ be a set of $n\times m$ valuation matrices with nonnegative entries, and let $B_1,\dots,B_n\ge 0$ be the budgets. Let $(\mathbf z,\mathbf x^*,\xi^*,\eta^*,\theta^*,\tilde{\mathbf u}^1,\dots,\tilde{\mathbf u}^n)$ be any choice of optimal solutions of the problems (12), (14) and (13) of Algorithm ROM.a, and let $r^*_{ij}=\xi^*_j+\eta^*_iz_{ij}+\theta^*_iz_{ij}$ be the reservation prices (15). Then
--
--   1. $\sum_{i\in\mathcal N}x^*_{ij}\le 1$ for all $j\in\mathcal M$; (22)
--   2. $\sum_{j\in\mathcal M}x^*_{ij}z_{ij}\le B_i$ for all $i\in\mathcal N$; (23)
--   3. $\sum_{j\in\mathcal M}x^*_{ij}z_{ij}\le\sum_{j\in\mathcal M}x^*_{ij}u_{ij}$ for all $\mathbf u\in\mathcal U$ and $i\in\mathcal N$; (24)
--   4. $x^*_{ij}r^*_{ij}=x^*_{ij}z_{ij}$ for all $i\in\mathcal N$, $j\in\mathcal M$; (25)
--   5. $\sum_{j\in\mathcal M}x^*_{ij}r^*_{ij}\le B_i$ for all $i\in\mathcal N$; (26)
--   6. the identity (27):
--   $$\sum_{i\in\mathcal N}\sum_{j\in\mathcal M}x^*_{ij}r^*_{ij}=\sum_{j\in\mathcal M}\xi^*_j+\sum_{i\in\mathcal N}\Bigl(\eta^*_iB_i+\sum_{j\in\mathcal M}x^*_{ij}\theta^*_i\tilde u^i_j\Bigr).$$
--
--   These relations are the common ground of the properties of ROM: (22)–(24) are the constraints satisfied by the nominal allocation, (25)–(26) say that the reservation prices charge the nominal allocation exactly its worst case value and within budget, and (27) identifies the total reserved revenue with the optimal value of (13).
--
--   **Formalization Note** Nonnegativity of the valuations in $\mathcal U$ and of the budgets is a standing assumption of the model that the paper uses without stating; it is made explicit here. The statement holds for every choice of optimal solutions of (12), (14) and (13), not for one particular selection.
-- source:
--   Bandi, Bertsimas, Optimal Design for Multi-Item Auctions: A Robust Optimization Approach, Math. Oper. Res. 39(4):1012–1038 (2014), p. 1020 (PDF p. 10), Proposition 2, Eqs. (22)–(27)

import Mathlib
import Definitions.Def_RobustAuction_ROM_AuctionLP
import Definitions.Def_RobustAuction_ROM_Mechanism

namespace RobustAuction.ROM

open Finset

/-- Proposition 2 (Bandi–Bertsimas 2014, p. 1020): the quantities computed by ROM.a satisfy
(22)–(27), for every choice of optimal solutions of (12), (14), (13). Valuations in `U` and
budgets are nonnegative (standing assumptions of the model, implicit in the paper). -/
theorem proposition_2 {n m : ℕ} (U : Set (Fin n → Fin m → ℝ)) (B : Fin n → ℝ)
    (hU : ∀ u ∈ U, ∀ i j, 0 ≤ u i j) (hB : ∀ i, 0 ≤ B i)
    (d : ROMData n m) (hd : IsROMa U B d) :
    (∀ j, ∑ i, d.xs i j ≤ 1) ∧
    (∀ i, ∑ j, d.xs i j * d.z i j ≤ B i) ∧
    (∀ u ∈ U, ∀ i, ∑ j, d.xs i j * d.z i j ≤ ∑ j, d.xs i j * u i j) ∧
    (∀ i j, d.xs i j * rStar d i j = d.xs i j * d.z i j) ∧
    (∀ i, ∑ j, d.xs i j * rStar d i j ≤ B i) ∧
    (∑ i, ∑ j, d.xs i j * rStar d i j =
      ∑ j, d.ξ j + ∑ i, (d.η i * B i + ∑ j, d.xs i j * d.θ i * d.ut i i j)) := by sorry

end RobustAuction.ROM
