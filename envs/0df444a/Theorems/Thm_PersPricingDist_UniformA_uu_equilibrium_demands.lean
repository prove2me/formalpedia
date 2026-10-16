-- Prove2me | Theorems.Thm_PersPricingDist_UniformA_uu_equilibrium_demands
-- name    : PersPricingDist.UniformA.uu_equilibrium_demands
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T02:45:12.095485+00:00
-- url     : https://prove2.me/theorems/16ffebd8-1af1-4568-99df-a00a6ba3b9e8
-- title:
--   OA p. 2 — positive UU equilibrium demands
-- statement:
--   At the wholesale price $w^*_{UU}$ and its equilibrium retail prices, the masses of consumers buying from A and B are
--
--   $$D_A^*=\frac{2(2-v)+s(3-4v-s)}{2(4+5s)(1-s)}>0,\qquad D_B^*=\frac{(2+s)(v-s)}{s(4+5s)(1-s)}>0.$$
--
--   The positivity verifies that both channels are active in the equilibrium used for the profit calculation. **Formalization Note** The demands are Lebesgue masses of actual choice sets clipped to $[0,X]$, not the interior linear expressions used to derive these formulas.
-- source:
--   Jullien, Reisinger & Rey, Personalized Pricing and Distribution Strategies, authors' manuscript of March 2022 (Management Science, doi:10.1287/mnsc.2022.4437; PDF sha256 25a6c84ac0c48c6720f6a9e1f9b1f1ec516412c31dac044ac84c1d4c72dfc253), OA p. 2 (PDF 35)

import Mathlib
import Definitions.Def_PersPricingDist_UniformA_Setting

namespace PersPricingDist.UniformA

/-- The positive demands at the OA p. 2 wholesale and retail prices. -/
theorem uu_equilibrium_demands (M : Model) (hM : M.Standing) :
    M.DA_UU (M.pA_UU M.wUU) (M.pB_UU M.wUU) =
      (2 * (2 - M.v) + M.s * (3 - 4 * M.v - M.s)) /
        (2 * (4 + 5 * M.s) * (1 - M.s)) ∧
    0 < M.DA_UU (M.pA_UU M.wUU) (M.pB_UU M.wUU) ∧
    M.DB_UU (M.pA_UU M.wUU) (M.pB_UU M.wUU) =
      ((2 + M.s) * (M.v - M.s)) /
        (M.s * (4 + 5 * M.s) * (1 - M.s)) ∧
    0 < M.DB_UU (M.pA_UU M.wUU) (M.pB_UU M.wUU) := by sorry
end PersPricingDist.UniformA
