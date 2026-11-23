-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Conv_add
-- name    : ReciprocityTheory.ChartRestriction.L1.Conv.add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:08:12.291024+00:00
-- url     : https://prove2.me/theorems/b6418ced-b675-456d-97c5-e838fc95f19b
-- title:
--   Conv: add
-- statement:
--   The Conv construction uses the add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModEvalSer.lean#L44-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModEvalSer.lean#L44-L48

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_add

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

theorem ReciprocityTheory.ChartRestriction.L1.Conv.add {f g : PowerSeries ℂ} (hf : Conv f) (hg : Conv g) : Conv (f + g) := by sorry
