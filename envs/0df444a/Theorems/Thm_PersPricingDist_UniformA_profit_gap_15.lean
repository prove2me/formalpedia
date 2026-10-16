-- Prove2me | Theorems.Thm_PersPricingDist_UniformA_profit_gap_15
-- name    : PersPricingDist.UniformA.profit_gap_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T02:45:05.628802+00:00
-- url     : https://prove2.me/theorems/9659de5c-6326-4f27-92a5-78fe40e1b337
-- title:
--   (15), OA p. 4 — UP profit strictly exceeds UU profit
-- statement:
--   The two closed-form equilibrium industry profits satisfy
--
--   $$\Pi^*_{UP}-\Pi^*_{UU}=\frac{(s-v)^2}{4s}\frac{4+6s+s^2}{(4+5s)(1-s^2)}>0.$$
--
--   Together with the positive UU gain over mono distribution, this strict comparison implies the UP gain. **Formalization Note** This item is the algebraic comparison of the closed forms in (12) and (14); separate milestones identify those forms with the consumer-payment profits.
-- source:
--   Jullien, Reisinger & Rey, Personalized Pricing and Distribution Strategies, authors' manuscript of March 2022 (Management Science, doi:10.1287/mnsc.2022.4437; PDF sha256 25a6c84ac0c48c6720f6a9e1f9b1f1ec516412c31dac044ac84c1d4c72dfc253), OA p. 4, (15) (PDF 37)

import Mathlib
import Definitions.Def_PersPricingDist_UniformA_Setting

namespace PersPricingDist.UniformA

/-- The closed-form industry profits satisfy the strict comparison (15). -/
theorem profit_gap_15 (M : Model) (hM : M.Standing) :
    (M.s + 2 * M.s ^ 2 - 4 * M.v * M.s - 2 * M.v * M.s ^ 2 +
      2 * M.v ^ 2 + M.v ^ 2 * M.s) /
        (4 * M.s * (1 - M.s ^ 2)) -
      (M.s * (5 * M.s + 4 - M.s ^ 2) +
        4 * M.v * (1 + M.s) * (M.v - 2 * M.s)) /
        (4 * M.s * (1 - M.s) * (4 + 5 * M.s)) =
      (((M.s - M.v) ^ 2) / (4 * M.s)) *
        ((4 + 6 * M.s + M.s ^ 2) / ((4 + 5 * M.s) * (1 - M.s ^ 2))) ∧
    0 < (((M.s - M.v) ^ 2) / (4 * M.s)) *
        ((4 + 6 * M.s + M.s ^ 2) / ((4 + 5 * M.s) * (1 - M.s ^ 2))) := by sorry
end PersPricingDist.UniformA
