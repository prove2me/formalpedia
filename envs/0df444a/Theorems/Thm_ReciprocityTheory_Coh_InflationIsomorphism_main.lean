-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_InflationIsomorphism_main
-- name    : ReciprocityTheory.Coh.InflationIsomorphism.main
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:29:04.884799+00:00
-- url     : https://prove2.me/theorems/6a8b2514-d0ee-46cc-ac4d-e15d2494747a
-- title:
--   Inflation Isomorphism: main
-- statement:
--   The Inflation Isomorphism construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/InfIso.lean#L70-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/InfIso.lean#L70-L102

import Definitions.Def_ReciprocityTheory_GroupCohomology_CardLenStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
import Definitions.Def_ReciprocityTheory_GroupCohomology_ResNormalHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
import Definitions.Def_ReciprocityTheory_GroupCohomology_Section
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfIsoB
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function Topology
noncomputable section
universe u
open ReciprocityTheory.Coh.InflationIsomorphism
variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [LocallyCompactSpace G] {N : Subgroup G} [N.Normal]

theorem ReciprocityTheory.Coh.InflationIsomorphism.main (hN : IsClosed (N : Set G)) (hW : ∀ W : Subgroup N, IsOpen (W : Set N) → IsUnit (W.index : R))
    (n : ℕ) : ∀ (M : TRep R G) [DiscreteTopology M.V] (Q : TRep R (G ⧸ N)) (P : Pair Q M),
    IsInvRep M N Q P → Bijective (P.hom.H n) := by sorry
