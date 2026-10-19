-- Prove2me | Theorems.Thm_SoficGroups_KunThomFiberCoarea_singletonFirstEdges_subset_matching_union
-- name    : SoficGroups.KunThomFiberCoarea.singletonFirstEdges_subset_matching_union
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:24.345557+00:00
-- url     : https://prove2.me/theorems/30355caf-eb5c-4af8-9e86-447a21d8a19c
-- title:
--   SoficGroups.KunThomFiberCoarea.singletonFirstEdges_subset_matching_union
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea

theorem SoficGroups.KunThomFiberCoarea.singletonFirstEdges_subset_matching_union
    {V : Type*} [DecidableEq V]
    (U : Finset (V × V)) :
    singletonFirstEdges U ⊆
      matchedFiberEdges U ∪ nonSingletonSecondEdges U := by sorry
