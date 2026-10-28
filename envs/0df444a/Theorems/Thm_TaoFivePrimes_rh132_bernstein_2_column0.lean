-- Prove2me | Theorems.Thm_TaoFivePrimes_rh132_bernstein_2_column0
-- name    : TaoFivePrimes.rh132_bernstein_2_column0
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:39:28.722893+00:00
-- url     : https://prove2.me/theorems/a253931a-9e25-4c0a-8ce9-f339ddfcaa72
-- title:
--   Bernstein Column0 arithmetic for heights 133.8–134.4
-- statement:
--   For rows $i\in[0,2]$ and all 23 columns, the stored matrix B agrees exactly with the corresponding finite Bernstein change of basis. This is a finite rational identity for the candidate polynomial data.
-- source:
--   Exact rational Bernstein framework adapted from sometik179; the candidate xi polynomial uses the theta/Mellin framework due to Gabewhigham.

import Definitions.Def_TaoFivePrimes_RH132BernsteinNegative133p8To134p4
import Mathlib

theorem TaoFivePrimes.rh132_bernstein_2_column0 : ∀ i : Fin 3, ∀ j : Fin 23,
    RH132BernsteinNegative133p8To134p4.b ⟨0+i.val, by omega⟩ j = RH132BernsteinNegative133p8To134p4.transform 11 (fun u => RH132BernsteinNegative133p8To134p4.r u j) ⟨0+i.val, by omega⟩ := by sorry
