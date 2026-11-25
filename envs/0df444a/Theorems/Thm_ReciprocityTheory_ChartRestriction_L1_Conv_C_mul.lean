-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Conv_C_mul
-- name    : ReciprocityTheory.ChartRestriction.L1.Conv.C_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:42:31.9288+00:00
-- url     : https://prove2.me/theorems/44282f74-4f97-4563-8314-1162b10428da
-- title:
--   Conv: C mul
-- statement:
--   The Conv construction uses the C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModEvalSer.lean#L100-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModEvalSer.lean#L100-L104

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

theorem ReciprocityTheory.ChartRestriction.L1.Conv.C_mul {f : PowerSeries ℂ} (hf : Conv f) (c : ℂ) : Conv (PowerSeries.C c * f) := by sorry
