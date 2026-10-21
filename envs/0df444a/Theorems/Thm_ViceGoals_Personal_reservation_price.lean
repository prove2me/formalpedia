-- Prove2me | Theorems.Thm_ViceGoals_Personal_reservation_price
-- name    : ViceGoals.Personal.reservation_price
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:19.505871+00:00
-- url     : https://prove2.me/theorems/2f8c7efc-1227-4279-b0a8-30b8ca4d7001
-- title:
--   Personal-goal reservation price
-- statement:
--   Suppose $0\le p<v-\beta h$. After the consumer has chosen an optimal goal and the resulting optimal quantity, her anticipated utility is nonnegative exactly when the price does not exceed
--
--   $$\bar p=v-h-\frac{h(1-\beta)}{\sqrt{1+2\lambda}}.$$
--
--   This threshold determines whether the consumer purchases in the personal-goal regime.
--
--   **Formalization Note** The strict upper price bound excludes the zero-consumption case, where utility is zero at prices above the reservation price.
-- source:
--   Amaldoss & Harutyunyan, Pricing of Vice Goods for Goal-Driven Consumers, SSRN 4226237 (version of September 2022), p. 12 (PDF 13), §4.2, paragraph before (9)

import Mathlib
import Definitions.Def_ViceGoals_Personal_Model

namespace ViceGoals.Personal

theorem reservation_price (m : Params) (hm : m.Standing)
    (p G q : ℝ) (hp : 0 ≤ p) (hpmax : p < m.v - m.beta * m.h)
    (hG : IsOptGoal m p G) (hq : IsOptQty m G p q) :
    (0 ≤ U3 m G p q ↔ p ≤ pbar m) := by sorry

end ViceGoals.Personal
