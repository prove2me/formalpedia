-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_FiniteLevelCohomology_exists_level
-- name    : ReciprocityTheory.Coh.FiniteLevelCohomology.exists_level
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:57.71338+00:00
-- url     : https://prove2.me/theorems/01b23437-6f34-447a-b0d3-bd1e7a71564f
-- title:
--   Finite Level Cohomology: exists level
-- statement:
--   The Finite Level Cohomology construction uses the exists level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/FiniteLevel.lean#L72-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/FiniteLevel.lean#L72-L115

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
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem ReciprocityTheory.Coh.FiniteLevelCohomology.exists_level [CompactSpace G] [TotallyDisconnectedSpace G] (M : TRep R G)
    [DiscreteTopology M.V] (n : ℕ) (x : M.H n) :
    ∃ (N : Subgroup G) (_ : N.Normal), IsOpen (N : Set G) ∧ ∀ (Q : TRep R (G ⧸ N)) (P : Pair Q M),
      IsInvRep M N Q P → x ∈ LinearMap.range (P.hom.H n) := by sorry
