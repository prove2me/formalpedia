-- Prove2me | Theorems.Thm_PositivityTheory_CW_CompactGroupFacts_hilbert_schmidt_continuous
-- name    : PositivityTheory.CW.CompactGroupFacts.hilbert_schmidt_continuous
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:37.611004+00:00
-- url     : https://prove2.me/theorems/a2627351-ef06-474e-98d0-d696e901a5f1
-- title:
--   Compact Group Facts: hilbert schmidt continuous
-- statement:
--   The Compact Group Facts construction uses the hilbert schmidt continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/GroupFactsHolds.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/GroupFactsHolds.lean#L23-L25

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

theorem PositivityTheory.CW.CompactGroupFacts.hilbert_schmidt_continuous : Continuous (hs2 : Matrix (Fin n) (Fin n) ℂ → ℝ) := by sorry
