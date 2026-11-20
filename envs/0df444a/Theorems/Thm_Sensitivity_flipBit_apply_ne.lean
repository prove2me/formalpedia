-- Prove2me | Theorems.Thm_Sensitivity_flipBit_apply_ne
-- name    : Sensitivity.flipBit_apply_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:54:26.546414+00:00
-- url     : https://prove2.me/theorems/fb53ad44-2a44-46c2-9159-6687596c11dc
-- title:
--   Sensitivity: flip Bit apply ne
-- statement:
--   The Sensitivity construction uses the flip Bit apply ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Defs.lean#L34-L36
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Defs.lean#L34-L36

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_Sensitivity_Defs
set_option autoImplicit false
open Sensitivity
variable {n : ℕ}

theorem Sensitivity.flipBit_apply_ne (x : Fin n → Bool) (i : Fin n) {j : Fin n} (h : j ≠ i) :
    flipBit x i j = x j := by sorry
