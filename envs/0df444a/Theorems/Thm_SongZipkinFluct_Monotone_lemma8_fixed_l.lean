-- Prove2me | Theorems.Thm_SongZipkinFluct_Monotone_lemma8_fixed_l
-- name    : SongZipkinFluct.Monotone.lemma8_fixed_l
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:39:34.421873+00:00
-- url     : https://prove2.me/theorems/11fcada8-5f53-4076-8299-268911f05018
-- title:
--   §4.1, proof of Lemma 8 — for each fixed l ≥ 0, the demand D(l) is stochastically increasing in the initial world state
-- statement:
--   Assume the standing hypotheses of the model, Assumption 1 ($\alpha\bar c < p$) and Condition 1 for a partial order $\preceq$ on the world states. Let $f_i(\cdot \mid l)$ be the law of the demand $D(l)$ in $(0,l]$ given $A(0) = i$. Then for $i \preceq j$ and every fixed $l \ge 0$,
--   $$D(l)\,\big|\,\{A(0)=i\} \;\le_{st}\; D(l)\,\big|\,\{A(0)=j\},$$
--   that is, $\sum_{e\ge d} f_i(e\mid l) \le \sum_{e \ge d} f_j(e \mid l)$ for every $d \ge 0$.
--
--   This is the fixed-lead-time form of Lemma 8, stated inside its proof. Lemma 9 needs this form, because $\Delta C$ carries the discount factor $e^{-\alpha L}$.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 360, §4.1, proof of Lemma 8 (unnumbered claim: "for any fixed l ≥ 0, we have D(l) ≤st D′(l)")

import Mathlib
import Definitions.Def_SongZipkinFluct_Monotone_Condition1

namespace SongZipkinFluct.Monotone

/-- **Lemma 8, fixed lead time** (Song and Zipkin 1993, §4.1, proof of Lemma 8, p. 360, unnumbered:
"Hence, for any fixed `l ≥ 0`, we have `D(l) ≤_st D′(l)`").

Under the standing hypotheses, Assumption 1 and Condition 1, for `i ⪯ j` and every `l ≥ 0`, the
demand in `(0, l]` given `A(0) = i` is stochastically smaller than the demand in `(0, l]` given
`A(0) = j`: `P(D(l) ≥ d | A(0) = i) ≤ P(D(l) ≥ d | A(0) = j)` for every `d`. -/
theorem lemma8_fixed_l {I : Type} [Countable I] [Nonempty I] [DecidableEq I] [PartialOrder I]
    (M : Model I) (hM : M.Standing) (hA : M.Assumption1) (hC : M.Condition1) :
    ∀ i j : I, i ≤ j → ∀ l : ℝ, 0 ≤ l →
      StLe (fun d => M.demandMass i d l) (fun d => M.demandMass j d l) := by sorry

end SongZipkinFluct.Monotone
