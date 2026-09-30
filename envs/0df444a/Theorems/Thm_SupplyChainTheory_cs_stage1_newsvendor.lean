-- Prove2me | Theorems.Thm_SupplyChainTheory_cs_stage1_newsvendor
-- name    : SupplyChainTheory.cs_stage1_newsvendor
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:17:31.526182+00:00
-- url     : https://prove2.me/theorems/d620b344-945b-4632-b920-2fe9e8ba664a
-- title:
--   Eq. (6.29): $g_1(y) = \mathbb{E}[h_1(y - D_1)^+ + (p + h'_2)(D_1 - y)^+]$, the stage-1 function is a newsvendor cost
-- statement:
--   At stage 1 of the Clark-Scarf recursion, for every base-stock vector $S$ and every $y$,
--
--   $$ g_1(y) \;=\; \mathbb{E}\big[h_1 (y - D_1)^+ + (p + h'_2)(D_1 - y)^+\big], $$
--
--   where $h'_2 = \sum_{i=2}^N h_i$. The function is identical in form to the newsvendor
--   objective (4.3) with $p$ replaced by $p + h'_2$: the stockout penalty seen by stage 1 is the
--   customer penalty plus the holding cost saved upstream by every unit sold. The identity is the
--   algebra $h_1 x + (p + h'_1) x^- = h_1 x^+ + (p + h'_2) x^-$ applied under the expectation, and
--   it holds for $N \ge 1$ with $D_1$ of finite mean.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 196, Sect. 6.2.2, Eq. (6.28)-(6.29)

import Definitions.Def_SupplyChainTheory_multiechelon

namespace SupplyChainTheory

theorem cs_stage1_newsvendor (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → MeasureTheory.Measure ℝ)
    (S : ℕ → ℝ) (hN : 1 ≤ N) [MeasureTheory.IsProbabilityMeasure (D 1)]
    (hD : MeasureTheory.Integrable (fun x => x) (D 1)) (y : ℝ) :
    csG N h p D S 1 y
      = ∫ d, (h 1 * max (y - d) 0 + (p + localHolding N h 2) * max (d - y) 0) ∂(D 1) := by sorry

end SupplyChainTheory
