-- Prove2me | Theorems.Thm_TaoFivePrimes_rh132_bernstein_3_lower
-- name    : TaoFivePrimes.rh132_bernstein_3_lower
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:38:42.22786+00:00
-- url     : https://prove2.me/theorems/b5c07b75-7ad9-4d68-af9a-430ec76adb9c
-- title:
--   Bernstein Lower arithmetic for heights 134.4–135
-- statement:
--   Every entry of the stored Bernstein matrix $B$ satisfies $B_{ij}\ge 14$. This is a finite exact rational inequality.
-- source:
--   Exact rational Bernstein framework adapted from sometik179; the candidate xi polynomial uses the theta/Mellin framework due to Gabewhigham.

import Definitions.Def_TaoFivePrimes_RH132BernsteinImag134p4To135
import Mathlib

theorem TaoFivePrimes.rh132_bernstein_3_lower : ∀ i : Fin 12, ∀ j : Fin 23,
    (14:ℚ)≤RH132BernsteinImag134p4To135.b i j := by sorry
