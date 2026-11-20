-- Prove2me | Theorems.Thm_Sensitivity_BoolFun_restrictTo_sensitivity_le
-- name    : Sensitivity.BoolFun.restrictTo_sensitivity_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:56:01.254657+00:00
-- url     : https://prove2.me/theorems/1991306b-f31b-4202-a393-5df632edadfe
-- title:
--   Bool Fun: restrict To sensitivity le
-- statement:
--   Sensitivity of the restriction is at most the sensitivity of f.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Subcube.lean#L67-L84
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Subcube.lean#L67-L84

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Multilinear
import Definitions.Def_Sensitivity_Subcube
set_option autoImplicit false
open Sensitivity
variable {n : ℕ}

theorem Sensitivity.BoolFun.restrictTo_sensitivity_le (f : BoolFun n) (free : Finset (Fin n))
    (base : Fin n → Bool) :
    (f.restrictTo free base).sensitivity ≤ f.sensitivity := by sorry
