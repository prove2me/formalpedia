-- Prove2me | Theorems.Thm_SoficGroups_SourceTopLevelCompressionFinal_exists_finitelyPresented_nonsofic_group
-- name    : SoficGroups.SourceTopLevelCompressionFinal.exists_finitelyPresented_nonsofic_group
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/44cf1952-2bed-4e48-af3f-00da3324a384
-- title:
--   SoficGroups.SourceTopLevelCompressionFinal.exists_finitelyPresented_nonsofic_group
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceTopLevelCompressionFinal
open SoficGroups.SourceTopLevelCompression
open SoficGroups.KunLiteralNineSourceFiniteModels

theorem SoficGroups.SourceTopLevelCompressionFinal.exists_finitelyPresented_nonsofic_group :
    ∃ (G : Type) (_ : Group G),
      Group.IsFinitelyPresented G ∧ ¬ SoficGroups.Sofic G := by sorry
