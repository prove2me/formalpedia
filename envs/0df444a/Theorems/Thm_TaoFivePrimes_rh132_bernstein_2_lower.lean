-- Prove2me | Theorems.Thm_TaoFivePrimes_rh132_bernstein_2_lower
-- name    : TaoFivePrimes.rh132_bernstein_2_lower
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:39:06.383659+00:00
-- url     : https://prove2.me/theorems/7e0c21b1-c84a-4af5-aef4-bd80baf80fc4
-- title:
--   Bernstein Lower arithmetic for heights 133.8–134.4
-- statement:
--   Every entry of the stored Bernstein matrix $B$ satisfies $B_{ij}\ge 6$. This is a finite exact rational inequality.
-- source:
--   Exact rational Bernstein framework adapted from sometik179; the candidate xi polynomial uses the theta/Mellin framework due to Gabewhigham.

import Definitions.Def_TaoFivePrimes_RH132BernsteinNegative133p8To134p4
import Mathlib

theorem TaoFivePrimes.rh132_bernstein_2_lower : ∀ i : Fin 12, ∀ j : Fin 23,
    (6:ℚ)≤RH132BernsteinNegative133p8To134p4.b i j := by sorry
