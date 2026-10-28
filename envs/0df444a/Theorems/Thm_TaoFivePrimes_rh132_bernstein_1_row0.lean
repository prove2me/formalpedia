-- Prove2me | Theorems.Thm_TaoFivePrimes_rh132_bernstein_1_row0
-- name    : TaoFivePrimes.rh132_bernstein_1_row0
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:06:56.037469+00:00
-- url     : https://prove2.me/theorems/6fcdc325-c6d0-40be-9b8f-fa83daa165fe
-- title:
--   Bernstein Row0 arithmetic for heights 133.2–133.8
-- statement:
--   For rows $i\in[0,2]$ and all 23 columns, the stored matrix R agrees exactly with the corresponding finite Bernstein change of basis. This is a finite rational identity for the candidate polynomial data.
-- source:
--   Exact rational Bernstein framework adapted from sometik179; the candidate xi polynomial uses the theta/Mellin framework due to Gabewhigham.

import Definitions.Def_TaoFivePrimes_RH132BernsteinImag133p2To133p8
import Mathlib

theorem TaoFivePrimes.rh132_bernstein_1_row0 : ∀ i : Fin 3, ∀ j : Fin 23,
    RH132BernsteinImag133p2To133p8.r ⟨0+i.val, by omega⟩ j = RH132BernsteinImag133p2To133p8.transform 22 (RH132BernsteinImag133p2To133p8.a ⟨0+i.val, by omega⟩) j := by sorry
