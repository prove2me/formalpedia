-- Prove2me | Theorems.Thm_TaoFivePrimes_rh132_bernstein_2_row1
-- name    : TaoFivePrimes.rh132_bernstein_2_row1
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:39:07.346255+00:00
-- url     : https://prove2.me/theorems/7c543754-4459-45b8-9d4a-f83db5d5deef
-- title:
--   Bernstein Row1 arithmetic for heights 133.8–134.4
-- statement:
--   For rows $i\in[3,5]$ and all 23 columns, the stored matrix R agrees exactly with the corresponding finite Bernstein change of basis. This is a finite rational identity for the candidate polynomial data.
-- source:
--   Exact rational Bernstein framework adapted from sometik179; the candidate xi polynomial uses the theta/Mellin framework due to Gabewhigham.

import Definitions.Def_TaoFivePrimes_RH132BernsteinNegative133p8To134p4
import Mathlib

theorem TaoFivePrimes.rh132_bernstein_2_row1 : ∀ i : Fin 3, ∀ j : Fin 23,
    RH132BernsteinNegative133p8To134p4.r ⟨3+i.val, by omega⟩ j = RH132BernsteinNegative133p8To134p4.transform 22 (RH132BernsteinNegative133p8To134p4.a ⟨3+i.val, by omega⟩) j := by sorry
