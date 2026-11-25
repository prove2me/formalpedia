-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_goodReduction_of_integral_unramified
-- name    : ReciprocityTheory.ChartRestriction.L1.goodReduction_of_integral_unramified
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:49:39.19159+00:00
-- url     : https://prove2.me/theorems/b34f05bc-ddb9-57e2-96a7-f72a2f319527
-- title:
--   L1: good Reduction of integral unramified
-- statement:
--   The L1 construction uses the good Reduction of integral unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedStatus.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedStatus.lean#L13-L18

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_Interface
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormWeierstrassCoeffSmallJ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_Norm1728EqOneOfFiveLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedStatus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.goodReduction_of_integral_unramified (hI : JInt) (hU : JUnram) : CM2 := by sorry
