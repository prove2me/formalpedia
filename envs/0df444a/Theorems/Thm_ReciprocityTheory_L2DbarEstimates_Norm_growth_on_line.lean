-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Norm_growth_on_line
-- name    : ReciprocityTheory.L2DbarEstimates.Norm.growth_on_line
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:00:31.907218+00:00
-- url     : https://prove2.me/theorems/a8bbeda4-e86c-59dc-860f-57f46307d796
-- title:
--   Norm: growth on line
-- statement:
--   The Norm construction uses the growth on line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SymmetricSections/NormVanishOfParts.lean#L9-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SymmetricSections/NormVanishOfParts.lean#L9-L31

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

theorem ReciprocityTheory.L2DbarEstimates.Norm.growth_on_line (n m : ℕ) (C : ℝ) (t : ℂ) (w : V n) :
    max (C * (1 + ‖t • w‖ ^ 2) ^ ((m : ℝ) / 2)) 0 ≤
      max C 0 * ((1 + ‖w‖) * (1 + ‖t‖)) ^ m := by sorry
