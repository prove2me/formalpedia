-- Prove2me | Theorems.Thm_Sensitivity_moebius_parity_sum
-- name    : Sensitivity.moebius_parity_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:59:24.974914+00:00
-- url     : https://prove2.me/theorems/6f3cedcc-87f9-4422-9e3d-9cc95e0bf956
-- title:
--   Sensitivity: moebius parity sum
-- statement:
--   Key identity: the parity-weighted sum relates to the top Möbius coefficient.
--       ∑_x f_pm(x) · parity(x) = 2 · (-1)^n · c_{univ}(f).
--
--       This follows from expanding the Möbius coefficients and using the
--       bijection between Boolean vectors and subsets.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Parity.lean#L168-L220
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Parity.lean#L168-L220

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

theorem Sensitivity.moebius_parity_sum (f : BoolFun n) (hn : 0 < n) :
    ∑ x : Fin n → Bool, f.paritySigned x =
    2 * (-1 : ℤ) ^ n * f.moebius Finset.univ := by sorry
