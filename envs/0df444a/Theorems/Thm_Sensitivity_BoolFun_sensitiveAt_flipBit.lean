-- Prove2me | Theorems.Thm_Sensitivity_BoolFun_sensitiveAt_flipBit
-- name    : Sensitivity.BoolFun.sensitiveAt_flipBit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:11:58.60379+00:00
-- url     : https://prove2.me/theorems/f81cb4bc-bed0-4aa4-8124-54698352f354
-- title:
--   Bool Fun: sensitive At flip Bit
-- statement:
--   Sensitivity at x is symmetric: if f is sensitive at x in direction i,
--       then f is sensitive at (flipBit x i) in direction i.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Basic.lean#L49-L53
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Basic.lean#L49-L53

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Basic
set_option autoImplicit false
open Sensitivity
variable {n : ℕ}

theorem Sensitivity.BoolFun.sensitiveAt_flipBit (f : BoolFun n) (x : Fin n → Bool) (i : Fin n) :
    f.sensitiveAt (flipBit x i) i ↔ f.sensitiveAt x i := by sorry
