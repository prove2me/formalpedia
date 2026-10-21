-- Prove2me | Theorems.Thm_ViceGoals_Personal_eq_10
-- name    : ViceGoals.Personal.eq_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:30.184901+00:00
-- url     : https://prove2.me/theorems/1ff3d8c8-132b-4b9a-be23-ad0e962e5f0f
-- title:
--   Equation (10): equilibrium price with personal goals
-- statement:
--   Let $p^*$ be a nonnegative, revenue-maximizing price when consumers set personal goals. Below the zero-demand threshold $h<v\sqrt{1+2\lambda}/(1-\beta+\sqrt{1+2\lambda})$, it is uniquely characterized by
--
--   $$p^*=\begin{cases}\dfrac{v+2v\lambda-h(\beta+2\lambda)}{2+4\lambda},&h\le h_0,\\v-h-\dfrac{h(1-\beta)}{\sqrt{1+2\lambda}},&h_0<h<\dfrac{v\sqrt{1+2\lambda}}{1-\beta+\sqrt{1+2\lambda}},\end{cases}$$
--
--   with $h_0$ as defined in the model. This price is compared with the benchmark equilibrium price in Proposition 1.
--
--   **Formalization Note** The upper endpoint is excluded because zero demand makes the price maximizer nonunique.
-- source:
--   Amaldoss & Harutyunyan, Pricing of Vice Goods for Goal-Driven Consumers, SSRN 4226237 (version of September 2022), pp. 13–14 (PDF 14–15), §4.2, (10) and definition of h0

import Mathlib
import Definitions.Def_ViceGoals_Personal_Model

namespace ViceGoals.Personal

theorem eq_10 (m : Params) (hm : m.Standing)
    (hhmax : m.h < m.v * Real.sqrt (1 + 2 * m.lam) /
      (1 - m.beta + Real.sqrt (1 + 2 * m.lam))) (p : ℝ) :
    IsEqPriceGoal m p ↔
      p = if m.h ≤ h0 m then
        (m.v + 2 * m.v * m.lam - m.h * (m.beta + 2 * m.lam)) /
          (2 + 4 * m.lam)
      else pbar m := by sorry

end ViceGoals.Personal
