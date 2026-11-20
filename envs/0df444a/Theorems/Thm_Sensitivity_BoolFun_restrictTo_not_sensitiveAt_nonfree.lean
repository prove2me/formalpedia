-- Prove2me | Theorems.Thm_Sensitivity_BoolFun_restrictTo_not_sensitiveAt_nonfree
-- name    : Sensitivity.BoolFun.restrictTo_not_sensitiveAt_nonfree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:55:47.404109+00:00
-- url     : https://prove2.me/theorems/9f0bc724-bd7e-4c97-8527-ae77bcdd2d30
-- title:
--   Bool Fun: restrict To not sensitive At nonfree
-- statement:
--   The restriction is not sensitive outside `free`.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Subcube.lean#L59-L64
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Subcube.lean#L59-L64

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Multilinear
import Definitions.Def_Sensitivity_Subcube
set_option autoImplicit false
open Sensitivity
variable {n : ℕ}

theorem Sensitivity.BoolFun.restrictTo_not_sensitiveAt_nonfree (f : BoolFun n) (free : Finset (Fin n))
    (base : Fin n → Bool) (x : Fin n → Bool) (i : Fin n) (hi : i ∉ free) :
    ¬(f.restrictTo free base).sensitiveAt x i := by sorry
