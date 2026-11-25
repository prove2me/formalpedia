-- Prove2me | Theorems.Thm_PositivityTheory_CW_basis_form_sum_of_gain
-- name    : PositivityTheory.CW.basis_form_sum_of_gain
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:51:16.049019+00:00
-- url     : https://prove2.me/theorems/776d9868-61d1-418d-a746-2ebcf317ba5a
-- title:
--   CW: basis form sum of gain
-- statement:
--   The CW construction uses the basis form sum of gain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/BasisSumOfOrthogonality.lean#L128-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/BasisSumOfOrthogonality.lean#L128-L211

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_BasisSumOfOrthogonality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW

theorem PositivityTheory.CW.basis_form_sum_of_gain : A0 → FunctionalCalculusLaws → A12 → BasisSumAsFormValues → A13 := by sorry
