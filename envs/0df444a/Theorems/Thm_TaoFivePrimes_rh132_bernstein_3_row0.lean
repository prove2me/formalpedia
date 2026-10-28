-- Prove2me | Theorems.Thm_TaoFivePrimes_rh132_bernstein_3_row0
-- name    : TaoFivePrimes.rh132_bernstein_3_row0
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:38:17.455975+00:00
-- url     : https://prove2.me/theorems/fe741cc5-67f4-4bd0-80f5-4b917f48ff58
-- title:
--   Bernstein Row0 arithmetic for heights 134.4–135
-- statement:
--   For rows $i\in[0,2]$ and all 23 columns, the stored matrix R agrees exactly with the corresponding finite Bernstein change of basis. This is a finite rational identity for the candidate polynomial data.
-- source:
--   Exact rational Bernstein framework adapted from sometik179; the candidate xi polynomial uses the theta/Mellin framework due to Gabewhigham.

import Definitions.Def_TaoFivePrimes_RH132BernsteinImag134p4To135
import Mathlib

theorem TaoFivePrimes.rh132_bernstein_3_row0 : ∀ i : Fin 3, ∀ j : Fin 23,
    RH132BernsteinImag134p4To135.r ⟨0+i.val, by omega⟩ j = RH132BernsteinImag134p4To135.transform 22 (RH132BernsteinImag134p4To135.a ⟨0+i.val, by omega⟩) j := by sorry
