-- Prove2me | Theorems.Thm_Sensitivity_BoolFun_localSensitivity_le_sensitivity
-- name    : Sensitivity.BoolFun.localSensitivity_le_sensitivity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:54:44.285705+00:00
-- url     : https://prove2.me/theorems/76b9aea1-8e94-434e-9f62-c1ed0ccac5df
-- title:
--   Bool Fun: local Sensitivity le sensitivity
-- statement:
--   The local sensitivity is at most the sensitivity.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Defs.lean#L87-L89
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Defs.lean#L87-L89

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_Sensitivity_Defs
set_option autoImplicit false
open Sensitivity
variable {n : ℕ}

theorem Sensitivity.BoolFun.localSensitivity_le_sensitivity (f : BoolFun n) (x : Fin n → Bool) :
    f.localSensitivity x ≤ f.sensitivity := by sorry
