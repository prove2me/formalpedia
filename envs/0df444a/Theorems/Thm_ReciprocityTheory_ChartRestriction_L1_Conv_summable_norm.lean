-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Conv_summable_norm
-- name    : ReciprocityTheory.ChartRestriction.L1.Conv.summable_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:55.359201+00:00
-- url     : https://prove2.me/theorems/35520e71-c259-4db9-a01e-9416f3540648
-- title:
--   Conv: summable norm
-- statement:
--   The Conv construction uses the summable norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModEvalSer.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModEvalSer.lean#L11-L14

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
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

theorem ReciprocityTheory.ChartRestriction.L1.Conv.summable_norm {f : PowerSeries ℂ} (hf : Conv f) {x : ℂ} (hx : ‖x‖ < 1) :
    Summable fun n => ‖PowerSeries.coeff n f * x ^ n‖ := by sorry
