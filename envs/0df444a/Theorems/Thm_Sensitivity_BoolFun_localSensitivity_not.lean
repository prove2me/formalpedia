-- Prove2me | Theorems.Thm_Sensitivity_BoolFun_localSensitivity_not
-- name    : Sensitivity.BoolFun.localSensitivity_not
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:11:51.813206+00:00
-- url     : https://prove2.me/theorems/6ec5bc9d-8945-4241-a2d8-1bddea041b87
-- title:
--   Bool Fun: local Sensitivity not
-- statement:
--   The local sensitivity of the complement equals the local sensitivity.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Basic.lean#L18-L24
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Basic.lean#L18-L24

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Basic
set_option autoImplicit false
open Sensitivity
variable {n : ℕ}

theorem Sensitivity.BoolFun.localSensitivity_not (f : BoolFun n) (x : Fin n → Bool) :
    BoolFun.localSensitivity (fun y => !f y) x = f.localSensitivity x := by sorry
