-- Prove2me | Theorems.Thm_Sensitivity_flipBit_apply_same
-- name    : Sensitivity.flipBit_apply_same
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:54:27.276995+00:00
-- url     : https://prove2.me/theorems/ad7fd772-72ca-493a-a94d-eeff21814e29
-- title:
--   Sensitivity: flip Bit apply same
-- statement:
--   The Sensitivity construction uses the flip Bit apply same property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Defs.lean#L29-L31
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Defs.lean#L29-L31

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_Sensitivity_Defs
set_option autoImplicit false
open Sensitivity
variable {n : ℕ}

theorem Sensitivity.flipBit_apply_same (x : Fin n → Bool) (i : Fin n) :
    flipBit x i i = !x i := by sorry
