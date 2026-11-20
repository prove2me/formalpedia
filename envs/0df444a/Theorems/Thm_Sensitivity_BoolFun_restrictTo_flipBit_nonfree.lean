-- Prove2me | Theorems.Thm_Sensitivity_BoolFun_restrictTo_flipBit_nonfree
-- name    : Sensitivity.BoolFun.restrictTo_flipBit_nonfree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:55:53.170558+00:00
-- url     : https://prove2.me/theorems/1103b963-28ea-42b0-b501-800e22d8b17c
-- title:
--   Bool Fun: restrict To flip Bit nonfree
-- statement:
--   Flipping a coordinate outside `free` doesn't change the restriction.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Subcube.lean#L52-L56
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Subcube.lean#L52-L56

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Multilinear
import Definitions.Def_Sensitivity_Subcube
set_option autoImplicit false
open Sensitivity
variable {n : ℕ}

theorem Sensitivity.BoolFun.restrictTo_flipBit_nonfree (f : BoolFun n) (free : Finset (Fin n))
    (base : Fin n → Bool) (x : Fin n → Bool) (i : Fin n) (hi : i ∉ free) :
    f.restrictTo free base (flipBit x i) = f.restrictTo free base x := by sorry
