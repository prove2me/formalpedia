-- Prove2me | Theorems.Thm_PositivityTheory_CW_CompactGroupFacts_mul_mem
-- name    : PositivityTheory.CW.CompactGroupFacts.mul_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:50:33.488846+00:00
-- url     : https://prove2.me/theorems/14f4e8a6-997d-4869-8c2b-693d43c6ce5e
-- title:
--   Compact Group Facts: mul mem
-- statement:
--   The Compact Group Facts construction uses the mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/GroupFactsHolds.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/GroupFactsHolds.lean#L14-L21

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

theorem PositivityTheory.CW.CompactGroupFacts.mul_mem (ε : Fin n → Bool) {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (hh : h ∈ UJset ε) :
    g * h ∈ UJset ε := by sorry
