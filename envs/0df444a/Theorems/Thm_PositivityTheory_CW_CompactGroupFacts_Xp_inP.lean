-- Prove2me | Theorems.Thm_PositivityTheory_CW_CompactGroupFacts_Xp_inP
-- name    : PositivityTheory.CW.CompactGroupFacts.Xp_inP
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:49:41.07109+00:00
-- url     : https://prove2.me/theorems/e216ae72-ea27-516d-8b29-24bb78729e20
-- title:
--   Compact Group Facts: Xp in P
-- statement:
--   The Compact Group Facts construction uses the Xp in P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/GroupFactsHolds.lean#L49-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/GroupFactsHolds.lean#L49-L73

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

theorem PositivityTheory.CW.CompactGroupFacts.Xp_inP (ε : Fin n → Bool) (p : Fin n × Fin n) (hp : p ∈ nc ε) : inP ε (Xp p.1 p.2) := by sorry
