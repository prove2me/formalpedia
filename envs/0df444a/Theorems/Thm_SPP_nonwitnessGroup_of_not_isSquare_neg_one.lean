-- Prove2me | Theorems.Thm_SPP_nonwitnessGroup_of_not_isSquare_neg_one
-- name    : SPP.nonwitnessGroup_of_not_isSquare_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:16:37.719598+00:00
-- url     : https://prove2.me/theorems/0a518f69-d91a-4b6f-b072-904758aa8941
-- title:
--   SPP: nonwitness Group of not is Square neg one
-- statement:
--   The SPP construction uses the nonwitness Group of not is Square neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Miscellaneous.lean#L14-L40
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Miscellaneous.lean#L14-L40

import Definitions.Def_MillerRabin_StrongProbable
import Definitions.Def_MillerRabin_Miscellaneous
set_option autoImplicit false
open Nat Subgroup
open SPP

theorem SPP.nonwitnessGroup_of_not_isSquare_neg_one {n : ℕ} (hn : 2 ≤ n) (ho : Odd n)
    (hn : ¬IsSquare (-1 : ZMod n)) :
    nonwitnessGroup n = comap (powMonoidHom (oddPart (n - 1))) (closure {-1}) := by sorry
