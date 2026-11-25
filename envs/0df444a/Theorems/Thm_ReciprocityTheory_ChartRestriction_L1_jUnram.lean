-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_jUnram
-- name    : ReciprocityTheory.ChartRestriction.L1.jUnram
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:06:42.893093+00:00
-- url     : https://prove2.me/theorems/99de5f82-d171-445f-bb81-12fa31ead4fe
-- title:
--   L1: j Unram
-- statement:
--   The L1 construction uses the j Unram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModJUnram.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModJUnram.lean#L15-L19

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_Interface
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_IsIntegralOfRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFixJ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModInertKur
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJUnram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.jUnram (hH : _root_.Neutral.HilbertClassField.Statement) (hC : ChebOmSt) : JUnram := by sorry
