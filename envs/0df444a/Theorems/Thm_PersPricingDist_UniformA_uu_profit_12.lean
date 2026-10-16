-- Prove2me | Theorems.Thm_PersPricingDist_UniformA_uu_profit_12
-- name    : PersPricingDist.UniformA.uu_profit_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T02:45:08.527685+00:00
-- url     : https://prove2.me/theorems/0618163d-d25d-4996-932b-ad8d1a84b857
-- title:
--   (12), OA p. 3 — UU industry profit exceeds mono profit
-- statement:
--   At the UU equilibrium with wholesale price $w^*_{UU}$, industry profit from the prices paid by consumers is
--
--   $$\Pi^*_{UU}=\frac{s(5s+4-s^2)+4v(1+s)(v-2s)}{4s(1-s)(4+5s)}.$$
--
--   Its gain over A's uniform-price monopoly profit is
--
--   $$\Pi^*_{UU}-\frac14=\frac{(1+s)(v-s)^2}{s(4+5s)(1-s)}>0.$$
--
--   This supplies the strict gain under uniform pricing by both firms. **Formalization Note** The left side is computed from choice-set demands; the displayed rational expression is a theorem, not its definition.
-- source:
--   Jullien, Reisinger & Rey, Personalized Pricing and Distribution Strategies, authors' manuscript of March 2022 (Management Science, doi:10.1287/mnsc.2022.4437; PDF sha256 25a6c84ac0c48c6720f6a9e1f9b1f1ec516412c31dac044ac84c1d4c72dfc253), OA p. 3, (12) (PDF 36)

import Mathlib
import Definitions.Def_PersPricingDist_UniformA_Setting

namespace PersPricingDist.UniformA

/-- The equilibrium UU industry profit and its strictly positive gain over
uniform-price mono distribution, equation (12) and OA p. 3. -/
theorem uu_profit_12 (M : Model) (hM : M.Standing) :
    M.indUU (M.pA_UU M.wUU) (M.pB_UU M.wUU) =
      (M.s * (5 * M.s + 4 - M.s ^ 2) +
        4 * M.v * (1 + M.s) * (M.v - 2 * M.s)) /
        (4 * M.s * (1 - M.s) * (4 + 5 * M.s)) ∧
    M.indUU (M.pA_UU M.wUU) (M.pB_UU M.wUU) - (1 : ℝ) / 4 =
      ((1 + M.s) * (M.v - M.s) ^ 2) /
        (M.s * (4 + 5 * M.s) * (1 - M.s)) ∧
    0 < M.indUU (M.pA_UU M.wUU) (M.pB_UU M.wUU) - (1 : ℝ) / 4 := by sorry
end PersPricingDist.UniformA
