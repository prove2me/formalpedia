-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Norm_normVanish_of_parts
-- name    : ReciprocityTheory.L2DbarEstimates.Norm.normVanish_of_parts
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:58:36.674436+00:00
-- url     : https://prove2.me/theorems/851710b5-0d8d-4504-bc2c-ccb6408d111c
-- title:
--   Norm: norm Vanish of parts
-- statement:
--   The Norm construction uses the norm Vanish of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SymmetricSections/NormVanishOfParts.lean#L33-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SymmetricSections/NormVanishOfParts.lean#L33-L78

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_HoloSectionStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_NormVanishOfParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Norm
open Filter Topology Asymptotics
universe u

theorem ReciprocityTheory.L2DbarEstimates.Norm.normVanish_of_parts (h1 : lineVanishStatement) (h2 : esymmZeroStatement)
    (h4 : symmDiffStatement.{u}) (h5 : symmVanishStatement.{u})
    (h6 : symmGrowthStatement.{u}) (h7 : lineFiniteStatement) :
    normVanishStatement.{u} := by sorry
