-- Prove2me | Theorems.Thm_SoficGroups_KunUniversalGoodRootReferenceCuts_reference_difference_le_symmDiff_add_missing
-- name    : SoficGroups.KunUniversalGoodRootReferenceCuts.reference_difference_le_symmDiff_add_missing
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/57178dc7-ce78-4e06-b888-d9c1189b538b
-- title:
--   SoficGroups.KunUniversalGoodRootReferenceCuts.reference_difference_le_symmDiff_add_missing
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunUniversalGoodRootReferenceCuts
open scoped symmDiff

theorem SoficGroups.KunUniversalGoodRootReferenceCuts.reference_difference_le_symmDiff_add_missing
    {α : Type*} [DecidableEq α]
    (U T W : Finset α) (hsub : T ⊆ W) :
    (U \ W).card + (W \ U).card ≤
      (U ∆ T).card + (W \ T).card := by sorry
