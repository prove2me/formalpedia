-- Prove2me | Theorems.Thm_StaticReusable_Guarantee_step_2a_C2
-- name    : StaticReusable.Guarantee.step_2a_C2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:01.289815+00:00
-- url     : https://prove2.me/theorems/6cd8bd8d-b072-4125-9147-2aaf03be27ab
-- title:
--   §3.1 Step 2a, p. 14 (C = 2) — R(z_1, z_2) equals the printed rational function and is at least 4/5
-- statement:
--   For $C = 2$ and all $z_1, z_2 \ge 0$,
--   $$R(z_1, z_2) = \frac{z_1^2 + 4z_1z_2 + 3z_1 + 4z_2^2 + 6z_2 + 2}{z_1^2 + 4z_1z_2 + 2z_1 + 5z_2^2 + 6z_2 + 2} \ge \frac45 .$$
--
--   This is the case $C = 2$ of the bound on the stock-in ratio; $4/5 > 15/19$.
--
--   **Formalization Note** The closed form is included as a conjunct; it equals the general definition of $R$ with $a_0 = 1$, $a_1 = 2$, $a_2 = 2$, after dividing numerator and denominator by $4$.
-- source:
--   Besbes, Elmachtoub and Sun, Static Pricing: Universal Guarantees for Reusable Resources, arXiv:1905.00731v3, p. 14, §3.1, Step 2a (case C = 2)

import Mathlib
import Definitions.Def_StaticReusable_Guarantee_Setting

open Finset

namespace StaticReusable.Guarantee

theorem step_2a_C2 (z : ℕ → ℝ) (hz1 : 0 ≤ z 1) (hz2 : 0 ≤ z 2) :
    R 2 z = (z 1 ^ 2 + 4 * z 1 * z 2 + 3 * z 1 + 4 * z 2 ^ 2 + 6 * z 2 + 2) /
        (z 1 ^ 2 + 4 * z 1 * z 2 + 2 * z 1 + 5 * z 2 ^ 2 + 6 * z 2 + 2) ∧
      (4 / 5 : ℝ) ≤ R 2 z := by sorry
end StaticReusable.Guarantee
