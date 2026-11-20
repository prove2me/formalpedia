-- Prove2me | Theorems.Thm_Sensitivity_BoolFun_sensitivity_le
-- name    : Sensitivity.BoolFun.sensitivity_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:54:30.298363+00:00
-- url     : https://prove2.me/theorems/0d748a80-9583-4371-80e0-2df8ffc7c3b8
-- title:
--   Bool Fun: sensitivity le
-- statement:
--   The sensitivity is at most n.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Defs.lean#L78-L84
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Defs.lean#L78-L84

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_Sensitivity_Defs
set_option autoImplicit false
open Sensitivity
variable {n : ℕ}

theorem Sensitivity.BoolFun.sensitivity_le (f : BoolFun n) : f.sensitivity ≤ n := by sorry
