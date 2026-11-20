-- Prove2me | Theorems.Thm_Sensitivity_BoolFun_sensitiveAt_of_paritySigned_eq
-- name    : Sensitivity.BoolFun.sensitiveAt_of_paritySigned_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:59:35.688342+00:00
-- url     : https://prove2.me/theorems/9fe07d91-8a7e-4443-84a4-7b61927b9a94
-- title:
--   Bool Fun: sensitive At of parity Signed eq
-- statement:
--   If paritySigned is the same at x and flipBit x i, then f is sensitive there.
--
--       Proof: parity flips sign under flipBit. If f_pm · parity stays the same,
--       f_pm must also flip, so f changes value.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Parity.lean#L108-L127
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Parity.lean#L108-L127

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Multilinear
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_Sensitivity_Parity
set_option autoImplicit false
open Sensitivity
variable {n : ℕ}

theorem Sensitivity.BoolFun.sensitiveAt_of_paritySigned_eq (f : BoolFun n)
    (x : Fin n → Bool) (i : Fin n)
    (h : f.paritySigned (flipBit x i) = f.paritySigned x) :
    f.sensitiveAt x i := by sorry
