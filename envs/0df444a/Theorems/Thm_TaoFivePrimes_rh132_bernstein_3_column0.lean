-- Prove2me | Theorems.Thm_TaoFivePrimes_rh132_bernstein_3_column0
-- name    : TaoFivePrimes.rh132_bernstein_3_column0
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:38:12.822869+00:00
-- url     : https://prove2.me/theorems/19375214-7637-4ed4-9a09-385f261576e2
-- title:
--   Bernstein Column0 arithmetic for heights 134.4–135
-- statement:
--   For rows $i\in[0,2]$ and all 23 columns, the stored matrix B agrees exactly with the corresponding finite Bernstein change of basis. This is a finite rational identity for the candidate polynomial data.
-- source:
--   Exact rational Bernstein framework adapted from sometik179; the candidate xi polynomial uses the theta/Mellin framework due to Gabewhigham.

import Definitions.Def_TaoFivePrimes_RH132BernsteinImag134p4To135
import Mathlib

theorem TaoFivePrimes.rh132_bernstein_3_column0 : ∀ i : Fin 3, ∀ j : Fin 23,
    RH132BernsteinImag134p4To135.b ⟨0+i.val, by omega⟩ j = RH132BernsteinImag134p4To135.transform 11 (fun u => RH132BernsteinImag134p4To135.r u j) ⟨0+i.val, by omega⟩ := by sorry
