-- Prove2me | Theorems.Thm_Sensitivity_BoolFun_exists_fullDegree_restriction
-- name    : Sensitivity.BoolFun.exists_fullDegree_restriction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:56:09.600056+00:00
-- url     : https://prove2.me/theorems/8ccf5c20-15ca-43a3-8316-8751b1d91ba5
-- title:
--   Bool Fun: exists full Degree restriction
-- statement:
--   Key lemma: if f has degree d ≥ 1, there exists S with |S| = d,
--       f.moebius S ≠ 0, and the restriction preserves the coefficient.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Subcube.lean#L113-L119
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Subcube.lean#L113-L119

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Multilinear
import Definitions.Def_Sensitivity_Subcube
set_option autoImplicit false
open Sensitivity
variable {n : ℕ}

theorem Sensitivity.BoolFun.exists_fullDegree_restriction (f : BoolFun n) (hd : 0 < f.degree) :
    ∃ S : Finset (Fin n),
      S.card = f.degree ∧
      f.moebius S ≠ 0 ∧
      (f.restrictTo S (fun _ => false)).moebius S ≠ 0 := by sorry
