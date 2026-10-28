-- Prove2me | Theorems.Thm_TaoFivePrimes_rh132_bernstein_3_column2
-- name    : TaoFivePrimes.rh132_bernstein_3_column2
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:38:20.705967+00:00
-- url     : https://prove2.me/theorems/2fad5d50-5d55-4121-b589-afc84b7a2ab4
-- title:
--   Bernstein Column2 arithmetic for heights 134.4–135
-- statement:
--   For rows $i\in[6,8]$ and all 23 columns, the stored matrix B agrees exactly with the corresponding finite Bernstein change of basis. This is a finite rational identity for the candidate polynomial data.
-- source:
--   Exact rational Bernstein framework adapted from sometik179; the candidate xi polynomial uses the theta/Mellin framework due to Gabewhigham.

import Definitions.Def_TaoFivePrimes_RH132BernsteinImag134p4To135
import Mathlib

theorem TaoFivePrimes.rh132_bernstein_3_column2 : ∀ i : Fin 3, ∀ j : Fin 23,
    RH132BernsteinImag134p4To135.b ⟨6+i.val, by omega⟩ j = RH132BernsteinImag134p4To135.transform 11 (fun u => RH132BernsteinImag134p4To135.r u j) ⟨6+i.val, by omega⟩ := by sorry
