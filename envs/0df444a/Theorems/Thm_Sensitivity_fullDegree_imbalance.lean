-- Prove2me | Theorems.Thm_Sensitivity_fullDegree_imbalance
-- name    : Sensitivity.fullDegree_imbalance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:59:37.773852+00:00
-- url     : https://prove2.me/theorems/2f09e97a-4215-485d-befc-88cb3934a5c5
-- title:
--   Sensitivity: full Degree imbalance
-- statement:
--   Imbalance: if the parity-weighted sum is nonzero, then one of the two
--       "parity-sign classes" has more than 2^{n-1} elements.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Parity.lean#L235-L305
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Parity.lean#L235-L305

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

theorem Sensitivity.fullDegree_imbalance (f : BoolFun n) (hn : 0 < n)
    (h : f.moebius Finset.univ ≠ 0) :
    ∃ c : ℤ, (c = 1 ∨ c = -1) ∧
      2 ^ (n - 1) < (Finset.univ.filter (fun x : Fin n → Bool =>
        f.paritySigned x = c)).card := by sorry
