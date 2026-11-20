-- Prove2me | Theorems.Thm_Sensitivity_BoolFun_exists_degree_witness
-- name    : Sensitivity.BoolFun.exists_degree_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:55:32.769312+00:00
-- url     : https://prove2.me/theorems/a764a647-7395-440e-b13b-0ff6a0b952c0
-- title:
--   Bool Fun: exists degree witness
-- statement:
--   If the degree is d > 0, there exists a set S of size d with nonzero coefficient.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Multilinear.lean#L67-L77
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Multilinear.lean#L67-L77

import Definitions.Def_Sensitivity_Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Int.Basic
import Definitions.Def_Sensitivity_Multilinear
set_option autoImplicit false
open Sensitivity
variable {n : ℕ}

theorem Sensitivity.BoolFun.exists_degree_witness (f : BoolFun n) (hd : 0 < f.degree) :
    ∃ S : Finset (Fin n), S.card = f.degree ∧ f.moebius S ≠ 0 := by sorry
