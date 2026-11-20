-- Prove2me | Theorems.Thm_Sensitivity_BoolFun_localSensitivity_le
-- name    : Sensitivity.BoolFun.localSensitivity_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:11:55.630538+00:00
-- url     : https://prove2.me/theorems/be1cbb39-e841-4876-ae2b-976f16f2457a
-- title:
--   Bool Fun: local Sensitivity le
-- statement:
--   Local sensitivity at x is at most n.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Basic.lean#L35-L40
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Basic.lean#L35-L40

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Basic
set_option autoImplicit false
open Sensitivity
variable {n : ℕ}

theorem Sensitivity.BoolFun.localSensitivity_le (f : BoolFun n) (x : Fin n → Bool) :
    f.localSensitivity x ≤ n := by sorry
