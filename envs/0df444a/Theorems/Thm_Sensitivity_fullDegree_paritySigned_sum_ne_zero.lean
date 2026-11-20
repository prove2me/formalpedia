-- Prove2me | Theorems.Thm_Sensitivity_fullDegree_paritySigned_sum_ne_zero
-- name    : Sensitivity.fullDegree_paritySigned_sum_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:59:23.249731+00:00
-- url     : https://prove2.me/theorems/6ce5b562-e3c6-4cbf-9205-753130bc92e5
-- title:
--   Sensitivity: full Degree parity Signed sum ne zero
-- statement:
--   If f has full degree (moebius at univ ≠ 0), the parity-weighted sum is nonzero.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Parity.lean#L223-L231
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Parity.lean#L223-L231

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

theorem Sensitivity.fullDegree_paritySigned_sum_ne_zero (f : BoolFun n) (hn : 0 < n)
    (h : f.moebius Finset.univ ≠ 0) :
    ∑ x : Fin n → Bool, f.paritySigned x ≠ 0 := by sorry
