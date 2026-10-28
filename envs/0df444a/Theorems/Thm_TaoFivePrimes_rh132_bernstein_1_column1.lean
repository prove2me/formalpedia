-- Prove2me | Theorems.Thm_TaoFivePrimes_rh132_bernstein_1_column1
-- name    : TaoFivePrimes.rh132_bernstein_1_column1
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:07:08.291364+00:00
-- url     : https://prove2.me/theorems/0cd4f2fb-dd2a-4cd5-be72-7554d8ed428c
-- title:
--   Bernstein Column1 arithmetic for heights 133.2–133.8
-- statement:
--   For rows $i\in[3,5]$ and all 23 columns, the stored matrix B agrees exactly with the corresponding finite Bernstein change of basis. This is a finite rational identity for the candidate polynomial data.
-- source:
--   Exact rational Bernstein framework adapted from sometik179; the candidate xi polynomial uses the theta/Mellin framework due to Gabewhigham.

import Definitions.Def_TaoFivePrimes_RH132BernsteinImag133p2To133p8
import Mathlib

theorem TaoFivePrimes.rh132_bernstein_1_column1 : ∀ i : Fin 3, ∀ j : Fin 23,
    RH132BernsteinImag133p2To133p8.b ⟨3+i.val, by omega⟩ j = RH132BernsteinImag133p2To133p8.transform 11 (fun u => RH132BernsteinImag133p2To133p8.r u j) ⟨3+i.val, by omega⟩ := by sorry
