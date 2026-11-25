-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_FiniteLevelCohomology_exists_nhds_right_const
-- name    : ReciprocityTheory.Coh.FiniteLevelCohomology.exists_nhds_right_const
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:50:21.298057+00:00
-- url     : https://prove2.me/theorems/fca48f38-d6e9-4c35-933c-90d750d729dc
-- title:
--   Finite Level Cohomology: exists nhds right const
-- statement:
--   The Finite Level Cohomology construction uses the exists nhds right const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/FiniteLevel.lean#L15-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/FiniteLevel.lean#L15-L29

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ResNormalHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Topology
open scoped Pointwise
universe u
open ReciprocityTheory.Coh.FiniteLevelCohomology

theorem ReciprocityTheory.Coh.FiniteLevelCohomology.exists_nhds_right_const {K X : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [TopologicalSpace X] [DiscreteTopology X] (f : K → X) (hf : Continuous f) :
    ∃ V ∈ 𝓝 (1 : K), ∀ g v, v ∈ V → f (g * v) = f g := by sorry
