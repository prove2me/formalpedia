-- Prove2me | Theorems.Thm_ViceGoals_Personal_eq_1
-- name    : ViceGoals.Personal.eq_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:21.579171+00:00
-- url     : https://prove2.me/theorems/6f803f55-75a7-458c-bf27-137603c002e8
-- title:
--   Equation (1): benchmark optimal purchase quantity
-- statement:
--   Let $q\ge0$ be the consumer's period-4 purchase quantity without a goal, at a nonnegative price $p$. Under the model's standing conditions, $q$ maximizes period-4 utility exactly when
--
--   $$q=\begin{cases}v-\beta h-p,&p\le v-\beta h,\\0,&p>v-\beta h.\end{cases}$$
--
--   This characterizes the quantity that the planning-stage consumer anticipates.
-- source:
--   Amaldoss & Harutyunyan, Pricing of Vice Goods for Goal-Driven Consumers, SSRN 4226237 (version of September 2022), p. 10 (PDF 11), §4.1, (1)

import Mathlib
import Definitions.Def_ViceGoals_Personal_Model

namespace ViceGoals.Personal

theorem eq_1 (m : Params) (hm : m.Standing) (p q : ℝ) (hp : 0 ≤ p) :
    IsOptQtyB m p q ↔
      q = if p ≤ m.v - m.beta * m.h then m.v - m.beta * m.h - p else 0 := by sorry

end ViceGoals.Personal
