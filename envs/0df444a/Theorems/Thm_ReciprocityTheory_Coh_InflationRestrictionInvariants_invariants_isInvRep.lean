-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_invariants_isInvRep
-- name    : ReciprocityTheory.Coh.InflationRestrictionInvariants.invariants_isInvRep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:34.740745+00:00
-- url     : https://prove2.me/theorems/18dc6bef-b2be-4f8f-a9df-58d0433a8d00
-- title:
--   Inflation Restriction Invariants: invariants is Inv Rep
-- statement:
--   The Inflation Restriction Invariants construction uses the invariants is Inv Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/InfRes.lean#L39-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/InfRes.lean#L39-L45

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InnerHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants
open ReciprocityTheory.Gal Cx Function
universe u
noncomputable section
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem ReciprocityTheory.Coh.InflationRestrictionInvariants.invariants_isInvRep (M : TRep R G) (N : Subgroup G) [N.Normal] : IsInvRep M N (invQ M N) (invP M N) := by sorry
