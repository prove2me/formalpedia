-- Prove2me | Theorems.Thm_ViceGoals_Personal_eq_5
-- name    : ViceGoals.Personal.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:36.940862+00:00
-- url     : https://prove2.me/theorems/64cc6ecf-e3a0-431b-b849-8a00f4eb850a
-- title:
--   Equation (5): optimal consumption at a personal goal
-- statement:
--   At a nonnegative price $p$ and goal $G\ge0$, the consumer chooses $q\ge0$ to maximize period-4 utility including the penalty for exceeding $G$. The unique maximizing quantity is
--
--   $$q^*(G)=\begin{cases}\dfrac{v-p-\beta h+2\lambda G}{1+2\lambda},&p\le v-\beta h,\;G\le v-p-\beta h,\\v-p-\beta h,&p\le v-\beta h,\;G>v-p-\beta h,\\0,&p>v-\beta h.\end{cases}$$
--
--   This is the consumption choice anticipated when the personal goal is set.
-- source:
--   Amaldoss & Harutyunyan, Pricing of Vice Goods for Goal-Driven Consumers, SSRN 4226237 (version of September 2022), p. 12 (PDF 13), §4.2, (5)

import Mathlib
import Definitions.Def_ViceGoals_Personal_Model

namespace ViceGoals.Personal

theorem eq_5 (m : Params) (hm : m.Standing) (G p q : ℝ)
    (hG : 0 ≤ G) (hp : 0 ≤ p) :
    IsOptQty m G p q ↔
      q = if p ≤ m.v - m.beta * m.h then
        (if G ≤ m.v - p - m.beta * m.h then
          (m.v - p - m.beta * m.h + 2 * G * m.lam) / (1 + 2 * m.lam)
         else m.v - p - m.beta * m.h)
      else 0 := by sorry

end ViceGoals.Personal
