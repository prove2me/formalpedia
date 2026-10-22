-- Prove2me | Theorems.Thm_RobustAuction_ROM_rom_feasible
-- name    : RobustAuction.ROM.rom_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T19:33:31.298956+00:00
-- url     : https://prove2.me/theorems/11a40665-26eb-40b2-ab21-86b9d0632eb3
-- title:
--   Propositions 3–5 / proof of Theorem 1, p. 1025 — ROM's allocation and payments are feasible for the robust auction LP (5)
-- statement:
--   Let $\mathcal U$ be a set of $n\times m$ valuation matrices with nonnegative entries and let $B_1,\dots,B_n\ge 0$ be the budgets. Take any choice of optimal solutions of the problems (12), (13), (14) of Algorithm ROM.a and (16), (17) of Algorithm ROM.b. Let $a^{\mathbf v}$ and $p^{\mathbf v}$ be the resulting allocation (20) and payments (21). Then $(a,p)$ satisfies every constraint of the robust auction design LP (5) other than the revenue constraints (5)–(6). For all $\mathbf v\in\mathcal U$:
--
--   1. (7) $\sum_{i\in\mathcal N}a^{\mathbf v}_{ij}\le 1$ for all $j\in\mathcal M$;
--   2. $a^{\mathbf v}\ge 0$;
--   3. (8) for every buyer $i$ and every report $\mathbf u_i$ with $(\mathbf u_i,\mathbf v_{-i})\in\mathcal U$,
--   $$\sum_{j\in\mathcal M}v_{ij}\,a^{(\mathbf u_i,\mathbf v_{-i})}_{ij}-p^{(\mathbf u_i,\mathbf v_{-i})}_i-\sum_{j\in\mathcal M}v_{ij}\,a^{\mathbf v}_{ij}+p^{\mathbf v}_i\le 0;$$
--   4. (9) $p^{\mathbf v}_i\le B_i$ for all $i\in\mathcal N$;
--   5. (10) $p^{\mathbf v}_i\le\sum_{j\in\mathcal M}v_{ij}\,a^{\mathbf v}_{ij}$ for all $i\in\mathcal N$.
--
--   The robust optimal mechanism is thus a feasible, incentive compatible, budget feasible and individually rational mechanism for every uncertainty set. This is the feasibility half of the paper's Theorem 1, whose proof states that "the feasibility follows from Propositions 3–5".
--
--   **Formalization Note** Nonnegative valuations and budgets are the model's standing assumptions, made explicit. No finiteness, boundedness or convexity of $\mathcal U$ is assumed; the existence of the optimal solutions is part of the hypothesis. The optimality half of Theorem 1, which asserts that ROM maximizes the worst case revenue, is false as printed and is not asserted here.
-- source:
--   Bandi, Bertsimas, Optimal Design for Multi-Item Auctions: A Robust Optimization Approach, Math. Oper. Res. 39(4):1012–1038 (2014), p. 1025 (PDF p. 15), proof of Theorem 1(a) ("the feasibility follows from Propositions 3–5"); Propositions 3–5, pp. 1021–1023 (PDF pp. 11–13); constraints (7)–(10), p. 1017

import Mathlib
import Definitions.Def_RobustAuction_ROM_AuctionLP
import Definitions.Def_RobustAuction_ROM_Mechanism

namespace RobustAuction.ROM

/-- Propositions 3–5 combined (Bandi–Bertsimas 2014, proof of Theorem 1, p. 1025: "the
feasibility follows from Propositions 3–5"): ROM's allocation (20) and payments (21) satisfy
every constraint of the robust auction LP (5) other than the revenue constraints (5)–(6) —
(7), `x ≥ 0`, (8), (9) and (10) — for every choice of optimal solutions of (12)–(14), (16),
(17). Valuations in `U` and budgets are nonnegative (standing assumptions of the model). -/
theorem rom_feasible {n m : ℕ} (U : Set (Fin n → Fin m → ℝ)) (B : Fin n → ℝ)
    (hU : ∀ u ∈ U, ∀ i j, 0 ≤ u i j) (hB : ∀ i, 0 ≤ B i)
    (d : ROMData n m) (hd : IsROM U B d) :
    IsFeasibleMechanism U B (alloc U d) (pay U d) := by sorry

end RobustAuction.ROM
