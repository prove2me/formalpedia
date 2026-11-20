-- Prove2me | Theorems.Thm_Sensitivity_BoolFun_restrictTo_moebius_subset
-- name    : Sensitivity.BoolFun.restrictTo_moebius_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:56:02.216296+00:00
-- url     : https://prove2.me/theorems/c412f1f7-fd57-45b1-8428-5bd4e131697b
-- title:
--   Bool Fun: restrict To moebius subset
-- statement:
--   When we restrict with base = false, the Möbius coefficient at
--       S ⊆ free is preserved.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Subcube.lean#L101-L109
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Subcube.lean#L101-L109

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Multilinear
import Definitions.Def_Sensitivity_Subcube
set_option autoImplicit false
open Sensitivity
variable {n : ℕ}

theorem Sensitivity.BoolFun.restrictTo_moebius_subset (f : BoolFun n) (free : Finset (Fin n))
    (S : Finset (Fin n)) (hS : S ⊆ free) :
    (f.restrictTo free (fun _ => false)).moebius S = f.moebius S := by sorry
