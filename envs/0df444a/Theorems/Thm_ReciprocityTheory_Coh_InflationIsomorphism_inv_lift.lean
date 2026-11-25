-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_InflationIsomorphism_inv_lift
-- name    : ReciprocityTheory.Coh.InflationIsomorphism.inv_lift
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:52:16.295799+00:00
-- url     : https://prove2.me/theorems/78057c61-c45c-4e18-a4a6-5d25de50b391
-- title:
--   Inflation Isomorphism: inv lift
-- statement:
--   The Inflation Isomorphism construction uses the inv lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/InfIsoA.lean#L46-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/InfIsoA.lean#L46-L83

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

theorem ReciprocityTheory.Coh.InflationIsomorphism.inv_lift [CompactSpace G] (N : Subgroup G) (hN : IsClosed (N : Set G))
    (hW : ∀ W : Subgroup N, IsOpen (W : Set N) → IsUnit (W.index : R))
    (A B : TRep R G) [DiscreteTopology A.V] (p : A.V →ₗ[R] B.V)
    (hp : ∀ g a, p (A.rho g a) = B.rho g (p a)) (hs : Surjective p) (b : B.V)
    (hb : ∀ g ∈ N, B.rho g b = b) : ∃ a, (∀ g ∈ N, A.rho g a = a) ∧ p a = b := by sorry
