-- Prove2me | Theorems.Thm_PersPricingDist_UniformA_up_profit_14
-- name    : PersPricingDist.UniformA.up_profit_14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T02:45:01.916665+00:00
-- url     : https://prove2.me/theorems/526e9a9c-3c52-4be3-90d1-7c41fb844228
-- title:
--   (13)–(14), OA p. 3 — UP industry profit
-- statement:
--   At $w^*_{UP}=s(1+v)/[2(1+s)]$ and A's leader price $p_A(w^*_{UP})=w^*_{UP}+(1-v)/2$, the industry profit is
--
--   $$\Pi^*_{UP}=\frac{s+2s^2-4vs-2vs^2+2v^2+v^2s}{4s(1-s^2)}.$$
--
--   This evaluates the actual consumer payments from the selected personalized-price response. **Formalization Note** The integral over $[0,X]$ defines industry profit; the rational expression is the calculated result.
-- source:
--   Jullien, Reisinger & Rey, Personalized Pricing and Distribution Strategies, authors' manuscript of March 2022 (Management Science, doi:10.1287/mnsc.2022.4437; PDF sha256 25a6c84ac0c48c6720f6a9e1f9b1f1ec516412c31dac044ac84c1d4c72dfc253), OA p. 3, (13)–(14) (PDF 36)

import Mathlib
import Definitions.Def_PersPricingDist_UniformA_Setting

namespace PersPricingDist.UniformA

/-- Actual consumer payments in the UP outcome equal the closed form (14). -/
theorem up_profit_14 (M : Model) (hM : M.Standing) :
    M.indUP M.wUP (M.pA_UP M.wUP) =
      (M.s + 2 * M.s ^ 2 - 4 * M.v * M.s - 2 * M.v * M.s ^ 2 +
        2 * M.v ^ 2 + M.v ^ 2 * M.s) /
        (4 * M.s * (1 - M.s ^ 2)) := by sorry
end PersPricingDist.UniformA
