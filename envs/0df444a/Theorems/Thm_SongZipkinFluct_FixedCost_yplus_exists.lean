-- Prove2me | Theorems.Thm_SongZipkinFluct_FixedCost_yplus_exists
-- name    : SongZipkinFluct.FixedCost.yplus_exists
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-06T05:51:05.717364+00:00
-- url     : https://prove2.me/theorems/59fb2bf2-0b48-44f1-a83b-67f1c9711f8e
-- title:
--   Existence of $y^+(i)$ and $y^+_{\min}$ — the myopic cost $G^+(i,\cdot)$ has a smallest minimizer, and $\min_i y^+(i)$ exists
-- statement:
--   Consider the fluctuating-demand inventory model under the standing hypotheses and Assumption 1 ($\alpha\bar c < p$). Recall the myopic cost
--   $$G^+(i,y) = (1-\gamma)\,c\,y + \beta\, C(i,y), \qquad y\in\mathbb Z,$$
--   where $C(i,y)$ is the expected discounted holding/backorder cost rate at the end of a lead time.
--
--   **Claim.** (1) For every world state $i$, $G^+(i,\cdot)$ has a smallest global minimizer $y^+(i)$ (the paper defines $y^+(i)$ as the smallest value of $y$ minimizing $G^+(i,y)$, which exists since $G^+(i,\cdot)$ is convex and coercive, Lemmas 1–2). (2) For any such family $\{y^+(i)\}_{i\in I}$ the minimum $y^+_{\min} = \min_{i\in I} y^+(i)$ is attained.
--
--   The paper takes both existence claims for granted when it defines these quantities; they are needed for the bounds $r^{--}$ and Lemma 6(c).
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, pp. 356–357 (definition of y⁺(i) p. 356 via Lemmas 1–2 p. 355; y⁺_min = min_i y⁺(i) p. 357)

import Mathlib
import Definitions.Def_SongZipkinFluct_FixedCost_Bounds

namespace SongZipkinFluct.FixedCost

open Model

/-- Song and Zipkin (1993), pp. 356–357: under the standing hypotheses and Assumption 1
(`αc̄ < p`), for every world state `i` the myopic cost `G⁺(i, ·)` has a smallest global
minimizer `y⁺(i)` (it is convex and coercive, Lemmas 1–2, p. 355), and for any such choice
`y⁺_min = min_i y⁺(i)` exists. -/
theorem yplus_exists {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] (M : Model I)
    (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) :
    (∃ yplus, IsYPlus M yplus) ∧ ∀ yplus, IsYPlus M yplus → ∃ ymin, IsYPlusMin yplus ymin := by
  sorry

end SongZipkinFluct.FixedCost
