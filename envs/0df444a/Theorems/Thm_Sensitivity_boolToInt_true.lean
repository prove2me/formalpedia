-- Prove2me | Theorems.Thm_Sensitivity_boolToInt_true
-- name    : Sensitivity.boolToInt_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:55:00.145184+00:00
-- url     : https://prove2.me/theorems/96d3bddf-f548-4f9f-b466-9d8f8e6c7307
-- title:
--   Sensitivity: bool To Int true
-- statement:
--   The Sensitivity construction uses the bool To Int true property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Multilinear.lean#L44-L44
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Multilinear.lean#L44-L44

import Definitions.Def_Sensitivity_Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Int.Basic
import Definitions.Def_Sensitivity_Multilinear
set_option autoImplicit false
open Sensitivity
variable {n : ℕ}

theorem Sensitivity.boolToInt_true : boolToInt true = 1 := by sorry

attribute [defeq] Sensitivity.boolToInt_true
