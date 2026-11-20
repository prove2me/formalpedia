-- Prove2me | Theorems.Thm_Sensitivity_parity_flipBit
-- name    : Sensitivity.parity_flipBit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:59:27.14984+00:00
-- url     : https://prove2.me/theorems/db0ff5ae-743b-496e-943c-bef7e399c10c
-- title:
--   Sensitivity: parity flip Bit
-- statement:
--   Flipping a bit negates the parity.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Parity.lean#L80-L102
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Parity.lean#L80-L102

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Multilinear
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_Sensitivity_Parity
set_option autoImplicit false
open Sensitivity
variable {n : ℕ}

theorem Sensitivity.parity_flipBit (x : Fin n → Bool) (i : Fin n) :
    parity (flipBit x i) = -parity x := by sorry
