-- Prove2me | Theorems.Thm_ViceGoals_Personal_eq_7
-- name    : ViceGoals.Personal.eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:31.616114+00:00
-- url     : https://prove2.me/theorems/d7c2a0f0-3aca-4e6b-ad18-153a51057c05
-- title:
--   Equation (7): optimal personal goal
-- statement:
--   Suppose $0\le p<v-\beta h$. A personal goal $G\ge0$ maximizes the period-3 utility obtained at the subsequent optimal quantity exactly when
--
--   $$G^*=\begin{cases}v-p-h,&p\le v-h,\\0,&v-h<p<v-\beta h.\end{cases}$$
--
--   The goal balances anticipated consumption against the future harm that the consumer fully counts when planning.
--
--   **Formalization Note** The strict upper price bound excludes the zero-consumption point, where every goal is optimal; $h>0$ excludes the analogous zero-harm multiplicity.
-- source:
--   Amaldoss & Harutyunyan, Pricing of Vice Goods for Goal-Driven Consumers, SSRN 4226237 (version of September 2022), p. 12 (PDF 13), §4.2, (7)

import Mathlib
import Definitions.Def_ViceGoals_Personal_Model

namespace ViceGoals.Personal

theorem eq_7 (m : Params) (hm : m.Standing) (hh : 0 < m.h)
    (p G : ℝ) (hp : 0 ≤ p) (hpmax : p < m.v - m.beta * m.h) :
    IsOptGoal m p G ↔
      G = if p ≤ m.v - m.h then m.v - p - m.h else 0 := by sorry

end ViceGoals.Personal
