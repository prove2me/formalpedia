-- Prove2me | Theorems.Thm_Sensitivity_BoolFun_degree_le
-- name    : Sensitivity.BoolFun.degree_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:56:00.234595+00:00
-- url     : https://prove2.me/theorems/fe767e67-01f2-4e0b-973a-a029b33bcec4
-- title:
--   Bool Fun: degree le
-- statement:
--   The degree is at most n.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Multilinear.lean#L60-L64
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Multilinear.lean#L60-L64

import Definitions.Def_Sensitivity_Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Int.Basic
import Definitions.Def_Sensitivity_Multilinear
set_option autoImplicit false
open Sensitivity
variable {n : ℕ}

theorem Sensitivity.BoolFun.degree_le (f : BoolFun n) : f.degree ≤ n := by sorry
