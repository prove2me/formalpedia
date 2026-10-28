-- Prove2me | Theorems.Thm_TaoFivePrimes_rh132_bernstein_2_column1
-- name    : TaoFivePrimes.rh132_bernstein_2_column1
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:39:08.174568+00:00
-- url     : https://prove2.me/theorems/8be193eb-8c62-4218-a0a9-9ea41c1e1408
-- title:
--   Bernstein Column1 arithmetic for heights 133.8–134.4
-- statement:
--   For rows $i\in[3,5]$ and all 23 columns, the stored matrix B agrees exactly with the corresponding finite Bernstein change of basis. This is a finite rational identity for the candidate polynomial data.
-- source:
--   Exact rational Bernstein framework adapted from sometik179; the candidate xi polynomial uses the theta/Mellin framework due to Gabewhigham.

import Definitions.Def_TaoFivePrimes_RH132BernsteinNegative133p8To134p4
import Mathlib

theorem TaoFivePrimes.rh132_bernstein_2_column1 : ∀ i : Fin 3, ∀ j : Fin 23,
    RH132BernsteinNegative133p8To134p4.b ⟨3+i.val, by omega⟩ j = RH132BernsteinNegative133p8To134p4.transform 11 (fun u => RH132BernsteinNegative133p8To134p4.r u j) ⟨3+i.val, by omega⟩ := by sorry
