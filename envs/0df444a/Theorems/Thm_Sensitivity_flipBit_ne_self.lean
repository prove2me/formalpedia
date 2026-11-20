-- Prove2me | Theorems.Thm_Sensitivity_flipBit_ne_self
-- name    : Sensitivity.flipBit_ne_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:54:27.625922+00:00
-- url     : https://prove2.me/theorems/da1c2dbe-d4ad-4d72-bc19-39045827af93
-- title:
--   Sensitivity: flip Bit ne self
-- statement:
--   The Sensitivity construction uses the flip Bit ne self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Defs.lean#L46-L50
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Defs.lean#L46-L50

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_Sensitivity_Defs
set_option autoImplicit false
open Sensitivity
variable {n : ℕ}

theorem Sensitivity.flipBit_ne_self (x : Fin n → Bool) (i : Fin n) :
    flipBit x i ≠ x := by sorry
