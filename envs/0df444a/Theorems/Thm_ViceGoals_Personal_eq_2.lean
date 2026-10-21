-- Prove2me | Theorems.Thm_ViceGoals_Personal_eq_2
-- name    : ViceGoals.Personal.eq_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:20.063879+00:00
-- url     : https://prove2.me/theorems/d1d31a3e-f040-4016-9f6b-3cb00a86756a
-- title:
--   Equation (2): benchmark demand and reservation price
-- statement:
--   Let $Q^B(p)$ be demand without a personal goal at a nonnegative price $p$. The consumer buys when anticipated period-2 utility is nonnegative. With reservation price $\bar p^B=v-h(2-\beta)$, demand is characterized by
--
--   $$Q^B(p)=\begin{cases}v-\beta h-p,&p\le\bar p^B,\\0,&p>\bar p^B.\end{cases}$$
--
--   The statement connects optimal consumption to the decision to purchase, including purchase at indifference.
-- source:
--   Amaldoss & Harutyunyan, Pricing of Vice Goods for Goal-Driven Consumers, SSRN 4226237 (version of September 2022), p. 10 (PDF 11), §4.1, (2)

import Mathlib
import Definitions.Def_ViceGoals_Personal_Model

namespace ViceGoals.Personal

theorem eq_2 (m : Params) (hm : m.Standing) (p Q : ℝ) (hp : 0 ≤ p) :
    IsDemandB m p Q ↔
      Q = if p ≤ pbarB m then m.v - m.beta * m.h - p else 0 := by sorry

end ViceGoals.Personal
