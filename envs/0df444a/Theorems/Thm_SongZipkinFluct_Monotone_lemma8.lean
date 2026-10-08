-- Prove2me | Theorems.Thm_SongZipkinFluct_Monotone_lemma8
-- name    : SongZipkinFluct.Monotone.lemma8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:40:00.807556+00:00
-- url     : https://prove2.me/theorems/104baad4-1ecd-4ee9-8837-0ab20a3c82cf
-- title:
--   Lemma 8 — the lead-time demand D^i_L is stochastically increasing in i
-- statement:
--   Assume the standing hypotheses of the model, Assumption 1 and Condition 1 for a partial order $\preceq$ on the world states. Let $D^i_L$ be the lead-time demand given $A(0) = i$, with law $P(D^i_L = d) = E[f_i(d \mid L)]$. Then
--   $$i \preceq j \implies D^i_L \le_{st} D^j_L,$$
--   that is, $P(D^i_L \ge d) \le P(D^j_L \ge d)$ for every $d \ge 0$.
--
--   This is the first link between the order on the world states and the costs: a higher world state produces stochastically more demand during a lead time.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 360, Lemma 8

import Mathlib
import Definitions.Def_SongZipkinFluct_Monotone_Condition1

namespace SongZipkinFluct.Monotone

/-- **Lemma 8** (Song and Zipkin 1993, §4.1, p. 360): "`D^i_L` is stochastically increasing in
`i`. That is, `i ⪯ j` implies `D^i_L ≤_st D^j_L`."

The lead-time demand `D^i_L` has the law `P(D^i_L = d) = E[f_i(d | L)]`. -/
theorem lemma8 {I : Type} [Countable I] [Nonempty I] [DecidableEq I] [PartialOrder I]
    (M : Model I) (hM : M.Standing) (hA : M.Assumption1) (hC : M.Condition1) :
    ∀ i j : I, i ≤ j → StLe (M.leadDemandMass i) (M.leadDemandMass j) := by sorry

end SongZipkinFluct.Monotone
