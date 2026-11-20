-- Prove2me | Theorems.Thm_Sensitivity_BoolFun_sensitiveAt_iff
-- name    : Sensitivity.BoolFun.sensitiveAt_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:11:53.895381+00:00
-- url     : https://prove2.me/theorems/73f7e41e-b001-47c2-a0ad-44a8c5026251
-- title:
--   Bool Fun: sensitive At iff
-- statement:
--   If f is sensitive at x in coordinate i, then flipping i gives a different value.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Basic.lean#L43-L45
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Basic.lean#L43-L45

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Basic
set_option autoImplicit false
open Sensitivity
variable {n : ℕ}

theorem Sensitivity.BoolFun.sensitiveAt_iff (f : BoolFun n) (x : Fin n → Bool) (i : Fin n) :
    f.sensitiveAt x i ↔ f (flipBit x i) ≠ f x := by sorry
