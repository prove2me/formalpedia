-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_norm
-- name    : ReciprocityTheory.L2DbarEstimates.norm
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:41:48.894849+00:00
-- url     : https://prove2.me/theorems/f8c23a03-bdd1-444c-a93c-a0c9e1777509
-- title:
--   L2 Dbar Estimates: norm
-- statement:
--   The L2 Dbar Estimates construction uses the norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/NormFibrations/ImportsAlt.lean#L11-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/NormFibrations/ImportsAlt.lean#L11-L28

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_NormFibrations_NormFib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_NormFibrations_NormOrd
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_NormVanishOfHoloSection
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_NormFibrations_ImportsAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open Filter Topology

theorem ReciprocityTheory.L2DbarEstimates.norm (n : ℕ) (M : Type u) [TopologicalSpace M] : NORMStatement n M := by sorry
