-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Conv_prod
-- name    : ReciprocityTheory.ChartRestriction.L1.Conv.prod
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:49:35.846921+00:00
-- url     : https://prove2.me/theorems/0c7b62f4-c82c-4eb1-ab28-3f5b2eb1efd6
-- title:
--   Conv: prod
-- statement:
--   The Conv construction uses the prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModEvalSer.lean#L90-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModEvalSer.lean#L90-L98

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LowUnit_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.Conv.prod {α : Type*} (s : Finset α) (f : α → PowerSeries ℂ) (hf : ∀ t ∈ s, Conv (f t)) :
    Conv (∏ t ∈ s, f t) := by sorry
