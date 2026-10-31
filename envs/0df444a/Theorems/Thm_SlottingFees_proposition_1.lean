-- Prove2me | Theorems.Thm_SlottingFees_proposition_1
-- name    : SlottingFees.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:51:40.417974+00:00
-- url     : https://prove2.me/theorems/812b03eb-98fd-4b49-89bd-a2dbbdd94696
-- title:
--   Proposition 1 — the low-variety subgame: assortment, fee $S^{|1|}$ (10) and profit $\Pi^{|1|}_r$ (corrected: endpoints of (11))
-- statement:
--   Consider the low-variety subgame ($|A|=1$) with slotting fees, under the standing assumptions $q_1>q_2$ and $q_l>c_l\ge0$, and write $r=v_1/(v_1+v_2)$. A subgame equilibrium exists, and in every one:
--
--   1. the retailer carries product 1 if $r\in[1/2,1]$ and product 2 if $r\in[0,1/2)$;
--   2. its slotting fee is
--   $$
--   S^{|1|}=\begin{cases}v_2/8 & r\in[0,3/7),\\ 0 & r\in[3/7,4/7],\\ v_1/8 & r\in(4/7,1];\end{cases}\qquad(10)
--   $$
--   3. its profit is
--   $$
--   \Pi^{|1|}_r=\begin{cases}v_2/16+S^{|1|}-K & r\in[0,3/7),\\ v_1/4-K & r\in[3/7,1/2),\\ v_2/4-K & r\in[1/2,4/7],\\ v_1/16+S^{|1|}-K & r\in(4/7,1].\end{cases}\qquad(11)
--   $$
--
--   When one product is only slightly more attractive, the retailer forgoes the slotting fee to keep both manufacturers competing for its single slot; otherwise it extracts the entrant's gross profit.
--
--   Differences from the source:
--   - correction: the rows of (11) on [0, 3/7], (3/7, 1/2), [1/2, 4/7), [4/7, 1] → on [0, 3/7), [3/7, 1/2), [1/2, 4/7], (4/7, 1]; reason: at r ∈ {3/7, 4/7}, where (10) gives S^{|1|} = 0, the printed rows give v_i/16 − K; at (q1, q2, c1, c2, K) = (4, 3, 0, 0, 0), r = 4/7, (11) gives 1/4 but the optimum is 3/4 (Corollary 1 at S = 0, or S = v1/8)
--   - reading: the retailer solves max over 0 ≤ S ≤ v_i/8 of Π̃_r(S) (p.12); when two fees are optimal, unspecified → the fee maximizes the retailer's profit over the fees at which the category is offered; the lowest maximizer is taken; reason: [0, v_i/8] is exactly the set of fees at which some manufacturer participates (Lemma 2); (10) prints S = 0 at r ∈ {3/7, 4/7}, where S = 0 and S = v_i/8 are both optimal
--   - reading: the |A| = 1 stage 2 of (5)-(8): the manufacturer that cannot enter offers its zero-profit price, the other solves (6)-(7) → IsStage2Outcome1: zero-profit price = least w ≥ c_l with non-negative profit; the entrant is the manufacturer whose zero-profit price gives the retailer the larger optimal gross profit, ties to manufacturer 1; (7) as the primitive condition that the retailer weakly prefers the entrant; reason: the paper does not say which manufacturer enters; this is its own logic (p.11) and makes the entrant the more attractive manufacturer of Lemma 2; (7) is equivalent to its closed form by Lemma 1
--   - encoding: the subgame equilibrium solved by backward induction (its outcome is 'the' equilibrium) → a subgame profile (retailer pricing after every wholesale price, stage-2 outcome after every fee, fee); the theorem asserts that such an equilibrium exists and that every one has the stated outcome; reason: subgame perfection made explicit; existence rules out a vacuous 'every equilibrium' statement
--   - encoding: retail-price problems (4) and (12) include the constants S − K and 2S − 2K → the optimal-price predicates maximize the gross profit only; reason: adding a constant does not change the maximizers
--   - encoding: r ∈ [0, 1] in the first and last rows → no lower bound 0 and no upper bound 1 on r; reason: r = v1/(v1 + v2) ∈ [0, 1] always holds under q_l > c_l ≥ 0
--   - encoding: products 1 and 2; Pr over θ ~ U[0,1] → indices 0 and 1 of Fin 2; Lebesgue measure of the set of types in [0,1], as a real number; reason: Lean convention; same instances
-- source:
--   Alan–Kurtuluş–Nakkas, Retail Category Management with Slotting Fees, MSOM (2024), doi:10.1287/msom.2022.0143, Proposition 1, (10)–(11), pp.12–13

import Mathlib
import Definitions.Def_SlottingFees_ClosedForms
import Definitions.Def_SlottingFees_Subgame1

namespace SlottingFees

/-- **Proposition 1**, pp.12–13 (Alan, Kurtuluş, Nakkas, MSOM 2024,
doi:10.1287/msom.2022.0143), corrected endpoints of (11): the `|A| = 1` subgame.

Under the standing assumptions an equilibrium of the `|A| = 1` subgame exists, and in every one,
with `r = v₁/(v₁ + v₂)`: the retailer carries product 1 if `r ∈ [1/2, 1]` and product 2 if
`r ∈ [0, 1/2)`; its fee is `S^{|1|} = v₂/8` on `[0, 3/7)`, `0` on `[3/7, 4/7]`, `v₁/8` on
`(4/7, 1]` (10); and its profit is `v₂/16 + S^{|1|} − K` on `[0, 3/7)`, `v₁/4 − K` on
`[3/7, 1/2)`, `v₂/4 − K` on `[1/2, 4/7]`, `v₁/16 + S^{|1|} − K` on `(4/7, 1]` ((11), corrected).

**Formalization Note** The paper's (11) uses `[0, 3/7]`, `(3/7, 1/2)`, `[1/2, 4/7)`, `[4/7, 1]`;
at `r ∈ {3/7, 4/7}` it then gives `v_i/16 − K` with `S^{|1|} = 0`, which is not the optimum
(at `(q₁, q₂, c₁, c₂, K) = (4, 3, 0, 0, 0)`, `r = 4/7`: (11) gives `1/4`, the optimum is `3/4`).
The endpoints are moved to the middle rows, where the value is continuous. `r ∈ [0, 1]` always
holds. Product 1 is `0`. -/
theorem proposition_1 (ω : Params) (hω : ω.Standing) :
    (∃ P : Play1, IsEq1 true ω P) ∧
    ∀ P : Play1, IsEq1 true ω P →
      (1 / 2 ≤ ω.ratio → ∃ w, P.outcome P.fee = some (0, w)) ∧
      (ω.ratio < 1 / 2 → ∃ w, P.outcome P.fee = some (1, w)) ∧
      (ω.ratio < 3 / 7 → P.fee = ω.v 1 / 8) ∧
      (3 / 7 ≤ ω.ratio → ω.ratio ≤ 4 / 7 → P.fee = 0) ∧
      (4 / 7 < ω.ratio → P.fee = ω.v 0 / 8) ∧
      (ω.ratio < 3 / 7 → P.value ω = ω.v 1 / 16 + P.fee - ω.K) ∧
      (3 / 7 ≤ ω.ratio → ω.ratio < 1 / 2 → P.value ω = ω.v 0 / 4 - ω.K) ∧
      (1 / 2 ≤ ω.ratio → ω.ratio ≤ 4 / 7 → P.value ω = ω.v 1 / 4 - ω.K) ∧
      (4 / 7 < ω.ratio → P.value ω = ω.v 0 / 16 + P.fee - ω.K) := by sorry

end SlottingFees
