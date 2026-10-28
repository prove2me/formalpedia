-- Prove2me | Theorems.Thm_TaoFivePrimes_rh132_bernstein_2_row0
-- name    : TaoFivePrimes.rh132_bernstein_2_row0
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:39:43.276215+00:00
-- url     : https://prove2.me/theorems/feb1cd29-3557-461c-ba05-54324a5a11af
-- title:
--   Bernstein Row0 arithmetic for heights 133.8–134.4
-- statement:
--   For rows $i\in[0,2]$ and all 23 columns, the stored matrix R agrees exactly with the corresponding finite Bernstein change of basis. This is a finite rational identity for the candidate polynomial data.
-- source:
--   Exact rational Bernstein framework adapted from sometik179; the candidate xi polynomial uses the theta/Mellin framework due to Gabewhigham.

import Definitions.Def_TaoFivePrimes_RH132BernsteinNegative133p8To134p4
import Mathlib

theorem TaoFivePrimes.rh132_bernstein_2_row0 : ∀ i : Fin 3, ∀ j : Fin 23,
    RH132BernsteinNegative133p8To134p4.r ⟨0+i.val, by omega⟩ j = RH132BernsteinNegative133p8To134p4.transform 22 (RH132BernsteinNegative133p8To134p4.a ⟨0+i.val, by omega⟩) j := by sorry
