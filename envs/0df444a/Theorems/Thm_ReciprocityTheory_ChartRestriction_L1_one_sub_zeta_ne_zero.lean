-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_one_sub_zeta_ne_zero
-- name    : ReciprocityTheory.ChartRestriction.L1.one_sub_zeta_ne_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:45:52.638817+00:00
-- url     : https://prove2.me/theorems/19f7b8fe-6233-4a9b-9350-0d0369533126
-- title:
--   L1: one sub zeta ne zero
-- statement:
--   The L1 construction uses the one sub zeta ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModFrobSer.lean#L111-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModFrobSer.lean#L111-L112

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobSer
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

theorem ReciprocityTheory.ChartRestriction.L1.one_sub_zeta_ne_zero {p : ℕ} (hp : p.Prime) : 1 - zetaC p ≠ 0 := by sorry
