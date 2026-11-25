-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_fac_bdd
-- name    : ReciprocityTheory.ChartRestriction.L1.fac_bdd
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:44:08.919483+00:00
-- url     : https://prove2.me/theorems/f61d0ff9-59c2-45f1-b158-ce49d0da97bc
-- title:
--   L1: fac bdd
-- statement:
--   The L1 construction uses the fac bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModGmForm.lean#L75-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModGmForm.lean#L75-L78

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

theorem ReciprocityTheory.ChartRestriction.L1.fac_bdd {t : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) : IsBoundedAtImInfty (fac t) := by sorry
