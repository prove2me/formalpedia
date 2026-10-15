-- Prove2me | Theorems.Thm_PiIrrationality_Bai_coef_le
-- name    : PiIrrationality.Bai.coef_le
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-14T19:56:04.518037+00:00
-- url     : https://prove2.me/theorems/37a45e4e-46d3-42b0-ad1f-197ad427dbe4
-- title:
--   Upper bound $\mathrm{coef}_n\le e^{15979.97420422751\,n}$
-- statement:
--   For every $n$,
--   $$\mathrm{coef}_n\le\exp(15979.97420422751\,n).$$
--
--   Role: bounds the $\pi$-coefficient $|V_n|$ from above (rate $5570r-\log 25-3716\log 2$ of Bai's (4.11)-(4.12)).
-- source:
--   Y. Bai, The irrationality measure of π is at most 7.101862832357, arXiv:2609.11276 (v2, 11 Sep 2026), https://arxiv.org/abs/2609.11276, (4.11)-(4.12)

import Definitions.Def_PiIrrationality_BaiForms
import Mathlib.Analysis.SpecialFunctions.Exp

theorem PiIrrationality.Bai.coef_le (n : ℕ) :
    (PiIrrationality.Bai.coef n : ℝ) ≤ Real.exp (15979.97420422751 * (n : ℝ)) := by
  sorry
