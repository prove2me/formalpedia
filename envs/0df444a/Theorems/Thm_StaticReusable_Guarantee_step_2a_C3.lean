-- Prove2me | Theorems.Thm_StaticReusable_Guarantee_step_2a_C3
-- name    : StaticReusable.Guarantee.step_2a_C3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:59.652361+00:00
-- url     : https://prove2.me/theorems/7185f307-65ec-49f1-82b9-938f1ece627b
-- title:
--   §3.1 Step 2a, p. 14 (C = 3) — R(z_1, z_2, z_3) ≥ 15/19
-- statement:
--   For $C = 3$ and all $z_1, z_2, z_3 \ge 0$,
--   $$R(z_1, z_2, z_3) \ge \frac{30}{38} = \frac{15}{19}.$$
--
--   This is the case $C = 3$ of the bound on the stock-in ratio, and the case in which the constant $15/19$ of Theorem 1 is attained in the limit.
--
--   **Formalization Note** The statement uses the general definition of $R$, not the expanded polynomials printed on p. 14; the printed denominator contains the typo "$30z_1z^{*2}_2$", which is $30 z_1 z_2^2$.
-- source:
--   Besbes, Elmachtoub and Sun, Static Pricing: Universal Guarantees for Reusable Resources, arXiv:1905.00731v3, p. 14, §3.1, Step 2a (case C = 3)

import Mathlib
import Definitions.Def_StaticReusable_Guarantee_Setting

open Finset

namespace StaticReusable.Guarantee

theorem step_2a_C3 (z : ℕ → ℝ) (hz : ∀ k ∈ Finset.Icc 1 3, 0 ≤ z k) :
    (15 / 19 : ℝ) ≤ R 3 z := by sorry
end StaticReusable.Guarantee
