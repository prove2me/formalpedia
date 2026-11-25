-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_evalSeries_rescaleExpand
-- name    : ReciprocityTheory.ChartRestriction.L1.evalSeries_rescaleExpand
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:43:35.674081+00:00
-- url     : https://prove2.me/theorems/903ea01b-8d8b-4f7b-a844-5533f9ede51e
-- title:
--   L1: eval Series rescale Expand
-- statement:
--   The L1 construction uses the eval Series rescale Expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModEvalSer.lean#L193-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModEvalSer.lean#L193-L197

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_sub1

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

theorem ReciprocityTheory.ChartRestriction.L1.evalSeries_rescaleExpand (f : PowerSeries ℂ) (c : ℂ) {k : ℕ} (hk : k ≠ 0) (x : ℂ) :
    ev (sub1 c k f) x = ev f (c * x ^ k) := by sorry
