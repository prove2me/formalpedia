-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Norm_normVanish_of_holoSection
-- name    : ReciprocityTheory.L2DbarEstimates.Norm.normVanish_of_holoSection
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:58:47.041955+00:00
-- url     : https://prove2.me/theorems/f56e05e1-c338-47bd-84b2-8c6e2fa3d64c
-- title:
--   Norm: norm Vanish of holo Section
-- statement:
--   The Norm construction uses the norm Vanish of holo Section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SymmetricSections/NormVanishOfHoloSection.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SymmetricSections/NormVanishOfHoloSection.lean#L14-L16

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_NormVanishOfParts
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_RemovableFinset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_EsymmZero
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_LineFinite
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_SymmGrowth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_SymmVanish
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_SymmDiff
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_Section
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_NormVanishOfHoloSection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Norm
universe u

theorem ReciprocityTheory.L2DbarEstimates.Norm.normVanish_of_holoSection (hsec : holoSectionStatement.{u}) : normVanishStatement.{u} := by sorry
