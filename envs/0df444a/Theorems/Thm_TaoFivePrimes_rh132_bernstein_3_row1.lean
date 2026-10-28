-- Prove2me | Theorems.Thm_TaoFivePrimes_rh132_bernstein_3_row1
-- name    : TaoFivePrimes.rh132_bernstein_3_row1
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:38:15.785826+00:00
-- url     : https://prove2.me/theorems/d65e33fe-3a92-4237-8dda-37373f521c8a
-- title:
--   Bernstein Row1 arithmetic for heights 134.4–135
-- statement:
--   For rows $i\in[3,5]$ and all 23 columns, the stored matrix R agrees exactly with the corresponding finite Bernstein change of basis. This is a finite rational identity for the candidate polynomial data.
-- source:
--   Exact rational Bernstein framework adapted from sometik179; the candidate xi polynomial uses the theta/Mellin framework due to Gabewhigham.

import Definitions.Def_TaoFivePrimes_RH132BernsteinImag134p4To135
import Mathlib

theorem TaoFivePrimes.rh132_bernstein_3_row1 : ∀ i : Fin 3, ∀ j : Fin 23,
    RH132BernsteinImag134p4To135.r ⟨3+i.val, by omega⟩ j = RH132BernsteinImag134p4To135.transform 22 (RH132BernsteinImag134p4To135.a ⟨3+i.val, by omega⟩) j := by sorry
