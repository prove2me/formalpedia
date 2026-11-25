-- Prove2me | Theorems.Thm_PositivityTheory_CW_CompactGroupFacts_isClosed_UJ
-- name    : PositivityTheory.CW.CompactGroupFacts.isClosed_UJ
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:50:40.529664+00:00
-- url     : https://prove2.me/theorems/6eb4375e-82a3-4061-bf46-93d1d8d46e86
-- title:
--   Compact Group Facts: is Closed UJ
-- statement:
--   The Compact Group Facts construction uses the is Closed UJ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/GroupFactsHolds.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/GroupFactsHolds.lean#L27-L30

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IsInLieAlgebraISmulAddConjTranspose
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_GroupFactsHolds
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
open PositivityTheory.CW.CompactGroupFacts
variable {n : ℕ}

theorem PositivityTheory.CW.CompactGroupFacts.isClosed_UJ (ε : Fin n → Bool) : IsClosed (UJset ε) := by sorry
