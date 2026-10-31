-- Prove2me | Theorems.Thm_SlottingFees_proposition_2
-- name    : SlottingFees.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:51:53.947988+00:00
-- url     : https://prove2.me/theorems/46060453-4f7a-466f-bdda-ec9c7895c0bb
-- title:
--   Proposition 2 — the high-variety subgame: fee $S^{|2|}$ (17) and profit $\Pi^{|2|}_r$ (18)
-- statement:
--   Consider the high-variety subgame ($|A|=2$) with slotting fees, under the standing assumptions, and write $r=v_1/(v_1+v_2)$ with $\bar v$, $v_{12}$, $S^{|2|}$ as in (17). A subgame equilibrium exists, and in every one the retailer sets the slotting fee $S^{|2|}$ and earns
--   $$
--   \Pi^{|2|}_r=\begin{cases}v_2/16-2K & r\in[0,\ q_2/(4q_1+q_2)],\\ q_1v_1/(4q_2)-2K & r\in(q_2/(4q_1+q_2),\ 1-\bar v],\\ v_{12}+2S^{|2|}-2K & r\in(1-\bar v,\ \bar v),\\ q_1v_2/(4q_2)-2K & r\in[\bar v,\ 4q_1/(4q_1+q_2)),\\ v_1/16-2K & r\in[4q_1/(4q_1+q_2),\ 1].\end{cases}\qquad(18)
--   $$
--
--   The retailer sets its fee to the gross profit of the manufacturer of the less attractive product; both products have positive demand exactly in the middle regime.
--
--   Differences from the source:
--   - reading: (w̃1, w̃2) solves (13) → a pure Nash equilibrium of (13) on w_l ≥ c_l in which each manufacturer takes its lowest best response; reason: best responses are unique when both demands are positive, so the selection only acts when a product has zero demand, where the rival at cost is the paper's 'price pressure' (p.16)
--   - encoding: the subgame equilibrium solved by backward induction (its outcome is 'the' equilibrium) → a subgame profile (retailer pricing after every wholesale price, stage-2 outcome after every fee, fee); the theorem asserts that such an equilibrium exists and that every one has the stated outcome; reason: subgame perfection made explicit; existence rules out a vacuous 'every equilibrium' statement
--   - encoding: retail-price problems (4) and (12) include the constants S − K and 2S − 2K → the optimal-price predicates maximize the gross profit only; reason: adding a constant does not change the maximizers
--   - encoding: r ∈ [0, 1] in the first and last rows → no lower bound 0 and no upper bound 1 on r; reason: r = v1/(v1 + v2) ∈ [0, 1] always holds under q_l > c_l ≥ 0
--   - encoding: products 1 and 2; Pr over θ ~ U[0,1] → indices 0 and 1 of Fin 2; Lebesgue measure of the set of types in [0,1], as a real number; reason: Lean convention; same instances
-- source:
--   Alan–Kurtuluş–Nakkas, Retail Category Management with Slotting Fees, MSOM (2024), doi:10.1287/msom.2022.0143, Proposition 2, (17)–(18), p.15

import Mathlib
import Definitions.Def_SlottingFees_ClosedForms
import Definitions.Def_SlottingFees_Subgame2

namespace SlottingFees

/-- **Proposition 2**, p.15 (Alan, Kurtuluş, Nakkas, MSOM 2024, doi:10.1287/msom.2022.0143): the
`|A| = 2` subgame.

Under the standing assumptions an equilibrium of the `|A| = 2` subgame exists, and in every one
the retailer's fee is `S^{|2|}` of (17) and, with `r = v₁/(v₁ + v₂)`, its profit is (18):

$$\Pi^{|2|}_r=\begin{cases}v_2/16-2K & r\in[0,\ q_2/(4q_1+q_2)],\\
q_1v_1/(4q_2)-2K & r\in(q_2/(4q_1+q_2),\ 1-\bar v],\\
v_{12}+2S^{|2|}-2K & r\in(1-\bar v,\ \bar v),\\
q_1v_2/(4q_2)-2K & r\in[\bar v,\ 4q_1/(4q_1+q_2)),\\
v_1/16-2K & r\in[4q_1/(4q_1+q_2),\ 1].\end{cases}$$

**Formalization Note** The stage-2 equilibrium selects each manufacturer's lowest best response
(`IsSelectedNE2`); this matters only in the rows where a product has zero demand. `r ∈ [0, 1]`
always holds. Products 1, 2 are `0`, `1`. -/
theorem proposition_2 (ω : Params) (hω : ω.Standing) :
    (∃ P : Play2, IsEq2 true ω P) ∧
    ∀ P : Play2, IsEq2 true ω P →
      P.fee = ω.S2 ∧
      (ω.ratio ≤ ω.q 1 / (4 * ω.q 0 + ω.q 1) → P.value ω = ω.v 1 / 16 - 2 * ω.K) ∧
      (ω.q 1 / (4 * ω.q 0 + ω.q 1) < ω.ratio → ω.ratio ≤ 1 - ω.vbar →
        P.value ω = ω.q 0 * ω.v 0 / (4 * ω.q 1) - 2 * ω.K) ∧
      (1 - ω.vbar < ω.ratio → ω.ratio < ω.vbar →
        P.value ω = ω.v12 + 2 * ω.S2 - 2 * ω.K) ∧
      (ω.vbar ≤ ω.ratio → ω.ratio < 4 * ω.q 0 / (4 * ω.q 0 + ω.q 1) →
        P.value ω = ω.q 0 * ω.v 1 / (4 * ω.q 1) - 2 * ω.K) ∧
      (4 * ω.q 0 / (4 * ω.q 0 + ω.q 1) ≤ ω.ratio → P.value ω = ω.v 0 / 16 - 2 * ω.K) := by sorry

end SlottingFees
