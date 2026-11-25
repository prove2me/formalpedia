-- Prove2me | Theorems.Thm_PositivityTheory_CW_eigenspaces_orthogonal_of_calculus
-- name    : PositivityTheory.CW.eigenspaces_orthogonal_of_calculus
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:47:37.518928+00:00
-- url     : https://prove2.me/theorems/5d356c8a-9301-5549-95af-8dbac9152c83
-- title:
--   CW: eigenspaces orthogonal of calculus
-- statement:
--   The CW construction uses the eigenspaces orthogonal of calculus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/EigenspacesOrthogonalOfCalculus.lean#L123-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/EigenspacesOrthogonalOfCalculus.lean#L123-L148

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_EigenspacesOrthogonalOfCalculus
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

theorem PositivityTheory.CW.eigenspaces_orthogonal_of_calculus : A0 → FunctionalCalculusLaws → EigenspacesOrthogonalAlt := by sorry
