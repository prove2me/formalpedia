-- Prove2me | Theorems.Thm_ViceGoals_Personal_eq_3
-- name    : ViceGoals.Personal.eq_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:24.192607+00:00
-- url     : https://prove2.me/theorems/cce17206-7cf9-4d66-ae67-69aff3f31cbe
-- title:
--   Equation (3): equilibrium benchmark price
-- statement:
--   Let $p^B$ be a nonnegative, revenue-maximizing price without personal goals. For $0\le h<v/(2-\beta)$, it is uniquely characterized by
--
--   $$p^B=\begin{cases}(v-\beta h)/2,&h\le v/(4-3\beta),\\v-h(2-\beta),&v/(4-3\beta)<h<v/(2-\beta).\end{cases}$$
--
--   This identifies the benchmark price against which the personal-goal price is compared.
--
--   **Formalization Note** The right endpoint is excluded because demand there is zero at every nonnegative price and the profit maximizer is not unique.
-- source:
--   Amaldoss & Harutyunyan, Pricing of Vice Goods for Goal-Driven Consumers, SSRN 4226237 (version of September 2022), p. 11 (PDF 12), §4.1, (3)

import Mathlib
import Definitions.Def_ViceGoals_Personal_Model

namespace ViceGoals.Personal

theorem eq_3 (m : Params) (hm : m.Standing)
    (hhmax : m.h < m.v / (2 - m.beta)) (p : ℝ) :
    IsEqPriceB m p ↔
      p = if m.h ≤ m.v / (4 - 3 * m.beta)
        then (m.v - m.beta * m.h) / 2
        else pbarB m := by sorry

end ViceGoals.Personal
