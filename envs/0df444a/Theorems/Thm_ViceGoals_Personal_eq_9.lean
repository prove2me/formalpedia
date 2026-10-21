-- Prove2me | Theorems.Thm_ViceGoals_Personal_eq_9
-- name    : ViceGoals.Personal.eq_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:42.377978+00:00
-- url     : https://prove2.me/theorems/355f7045-1b6b-461b-92c0-6cea842fa6f4
-- title:
--   Equation (9): demand with personal goals
-- statement:
--   Let $Q^*(p)$ be demand after a nonnegative price $p$, optimal personal-goal choice, and optimal consumption, with purchase at nonnegative anticipated utility. Then
--
--   $$Q^*(p)=\begin{cases}\dfrac{v-\beta h-p+2\lambda(v-h-p)}{1+2\lambda},&p\le\bar p,\\0,&p>\bar p,\end{cases}$$
--
--   where $\bar p=v-h-h(1-\beta)/\sqrt{1+2\lambda}$. This is the demand relation used in the firm's personal-goal pricing problem.
-- source:
--   Amaldoss & Harutyunyan, Pricing of Vice Goods for Goal-Driven Consumers, SSRN 4226237 (version of September 2022), p. 12 (PDF 13), §4.2, (9)

import Mathlib
import Definitions.Def_ViceGoals_Personal_Model

namespace ViceGoals.Personal

theorem eq_9 (m : Params) (hm : m.Standing) (p Q : ℝ) (hp : 0 ≤ p) :
    IsDemandGoal m p Q ↔
      Q = if p ≤ pbar m then
        (m.v - m.beta * m.h - p + 2 * (m.v - m.h - p) * m.lam) /
          (1 + 2 * m.lam)
      else 0 := by sorry

end ViceGoals.Personal
