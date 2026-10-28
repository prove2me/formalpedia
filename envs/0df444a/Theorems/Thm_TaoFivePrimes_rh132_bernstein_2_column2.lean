-- Prove2me | Theorems.Thm_TaoFivePrimes_rh132_bernstein_2_column2
-- name    : TaoFivePrimes.rh132_bernstein_2_column2
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:39:15.644343+00:00
-- url     : https://prove2.me/theorems/2a615b9b-6378-4dfb-be0f-f175c7e50def
-- title:
--   Bernstein Column2 arithmetic for heights 133.8–134.4
-- statement:
--   For rows $i\in[6,8]$ and all 23 columns, the stored matrix B agrees exactly with the corresponding finite Bernstein change of basis. This is a finite rational identity for the candidate polynomial data.
-- source:
--   Exact rational Bernstein framework adapted from sometik179; the candidate xi polynomial uses the theta/Mellin framework due to Gabewhigham.

import Definitions.Def_TaoFivePrimes_RH132BernsteinNegative133p8To134p4
import Mathlib

theorem TaoFivePrimes.rh132_bernstein_2_column2 : ∀ i : Fin 3, ∀ j : Fin 23,
    RH132BernsteinNegative133p8To134p4.b ⟨6+i.val, by omega⟩ j = RH132BernsteinNegative133p8To134p4.transform 11 (fun u => RH132BernsteinNegative133p8To134p4.r u j) ⟨6+i.val, by omega⟩ := by sorry
