-- Prove2me | Theorems.Thm_SongZipkinFluct_Monotone_lemma9
-- name    : SongZipkinFluct.Monotone.lemma9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:39:59.715579+00:00
-- url     : https://prove2.me/theorems/9711e650-e141-46d9-9f26-aaf266f6f956
-- title:
--   Lemma 9 — ΔC(i, y) is nonincreasing in the world state i
-- statement:
--   Assume the standing hypotheses of the model, Assumption 1 and Condition 1 for a partial order $\preceq$ on the world states. Let $C(i,y) = E[e^{-\alpha L}\hat C(y - D^i_L)]$ be the expected discounted inventory cost rate at the end of a lead time and $\Delta C(i,y) = C(i,y+1) - C(i,y)$. Then for every integer $y$,
--   $$i \preceq j \implies \Delta C(i,y) \ge \Delta C(j,y).$$
--
--   The marginal inventory cost of one more unit is smaller in a higher world state. This is the base case of the induction behind Theorem 7.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 360, Lemma 9

import Mathlib
import Definitions.Def_SongZipkinFluct_Monotone_Condition1

namespace SongZipkinFluct.Monotone

/-- **Lemma 9** (Song and Zipkin 1993, §4.1, p. 360): "`ΔC(i, y)` is nonincreasing in `i` for
fixed `y`, i.e., `ΔC(i, y) ≥ ΔC(j, y)` for `i ⪯ j`." -/
theorem lemma9 {I : Type} [Countable I] [Nonempty I] [DecidableEq I] [PartialOrder I]
    (M : Model I) (hM : M.Standing) (hA : M.Assumption1) (hC : M.Condition1) :
    ∀ (y : ℤ) (i j : I), i ≤ j → Δ M.costC j y ≤ Δ M.costC i y := by sorry

end SongZipkinFluct.Monotone
