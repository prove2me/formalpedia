-- Prove2me | Theorems.Thm_Sensitivity_indicator_not_mem
-- name    : Sensitivity.indicator_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:55:01.545196+00:00
-- url     : https://prove2.me/theorems/53dc95b4-15d9-4ebd-8e3c-b752a4c88e6d
-- title:
--   Sensitivity: indicator not mem
-- statement:
--   The Sensitivity construction uses the indicator not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Multilinear.lean#L37-L39
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Multilinear.lean#L37-L39

import Definitions.Def_Sensitivity_Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Int.Basic
import Definitions.Def_Sensitivity_Multilinear
set_option autoImplicit false
open Sensitivity
variable {n : ℕ}

theorem Sensitivity.indicator_not_mem {S : Finset (Fin n)} {i : Fin n} :
    indicator S i = false ↔ i ∉ S := by sorry
