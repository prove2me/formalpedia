-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_gmForm
-- name    : ReciprocityTheory.ChartRestriction.L1.gmForm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:59.323802+00:00
-- url     : https://prove2.me/theorems/50a84739-b6d8-4a71-8115-bef66cd3ffa6
-- title:
--   L1: gm Form
-- statement:
--   The L1 construction uses the gm Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModGmForm.lean#L120-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModGmForm.lean#L120-L132

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGmSlash
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGmForm
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

theorem ReciprocityTheory.ChartRestriction.L1.gmForm {m : ℕ} (hm : 0 < m) : IsMF (24 * ((Tm m).card : ℤ)) (Gm m) := by sorry
