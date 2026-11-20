-- Prove2me | Theorems.Thm_Sensitivity_indicator_mem
-- name    : Sensitivity.indicator_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:55:05.308182+00:00
-- url     : https://prove2.me/theorems/70dfb6f2-55e0-4117-9222-d75746f2391a
-- title:
--   Sensitivity: indicator mem
-- statement:
--   The Sensitivity construction uses the indicator mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Multilinear.lean#L32-L34
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Multilinear.lean#L32-L34

import Definitions.Def_Sensitivity_Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Int.Basic
import Definitions.Def_Sensitivity_Multilinear
set_option autoImplicit false
open Sensitivity
variable {n : ℕ}

theorem Sensitivity.indicator_mem {S : Finset (Fin n)} {i : Fin n} :
    indicator S i = true ↔ i ∈ S := by sorry
