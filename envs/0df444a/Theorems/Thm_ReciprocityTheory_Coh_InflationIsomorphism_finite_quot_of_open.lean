-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_InflationIsomorphism_finite_quot_of_open
-- name    : ReciprocityTheory.Coh.InflationIsomorphism.finite_quot_of_open
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:50:50.68673+00:00
-- url     : https://prove2.me/theorems/5d80766f-1017-53e2-8d19-46c0ca8c9fb1
-- title:
--   Inflation Isomorphism: finite quot of open
-- statement:
--   The Inflation Isomorphism construction uses the finite quot of open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/InfIsoA.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/InfIsoA.lean#L41-L44

import Definitions.Def_ReciprocityTheory_GroupCohomology_CardLenStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfIsoA
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
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem ReciprocityTheory.Coh.InflationIsomorphism.finite_quot_of_open {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] (W : Subgroup K) (hW : IsOpen (W : Set K)) : Finite (K ⧸ W) := by sorry
