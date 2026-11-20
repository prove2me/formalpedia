-- Prove2me | Theorems.Thm_Sensitivity_flipBit_injective
-- name    : Sensitivity.flipBit_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:54:29.15734+00:00
-- url     : https://prove2.me/theorems/545dc4d9-03c2-4c9f-9d00-580588c11b1b
-- title:
--   Sensitivity: flip Bit injective
-- statement:
--   The Sensitivity construction uses the flip Bit injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Defs.lean#L52-L59
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Defs.lean#L52-L59

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_Sensitivity_Defs
set_option autoImplicit false
open Sensitivity
variable {n : ℕ}

theorem Sensitivity.flipBit_injective (x : Fin n → Bool) : Function.Injective (flipBit x) := by sorry
