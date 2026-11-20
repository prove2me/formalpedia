-- Prove2me | Theorems.Thm_Sensitivity_BoolFun_sensitivity_not
-- name    : Sensitivity.BoolFun.sensitivity_not
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:11:52.228604+00:00
-- url     : https://prove2.me/theorems/b9f521f6-d9dd-4283-a5af-c4e0312ae438
-- title:
--   Bool Fun: sensitivity not
-- statement:
--   The sensitivity of the complement equals the sensitivity.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Basic.lean#L27-L32
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Basic.lean#L27-L32

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Basic
set_option autoImplicit false
open Sensitivity
variable {n : ℕ}

theorem Sensitivity.BoolFun.sensitivity_not (f : BoolFun n) :
    BoolFun.sensitivity (fun y => !f y) = f.sensitivity := by sorry
