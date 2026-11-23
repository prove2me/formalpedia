-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_FiniteLevelCohomology_exists_open_normal
-- name    : ReciprocityTheory.Coh.FiniteLevelCohomology.exists_open_normal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:03.966298+00:00
-- url     : https://prove2.me/theorems/e0bb486c-1d46-49c6-890a-6370efc76c25
-- title:
--   Finite Level Cohomology: exists open normal
-- statement:
--   The Finite Level Cohomology construction uses the exists open normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/FiniteLevel.lean#L39-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/FiniteLevel.lean#L39-L64

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

theorem ReciprocityTheory.Coh.FiniteLevelCohomology.exists_open_normal [CompactSpace G] [TotallyDisconnectedSpace G] (M : TRep R G)
    [DiscreteTopology M.V] {n : ℕ} (c : (Fin n → G) → M.V) (hc : Continuous c) :
    ∃ N : Subgroup G, N.Normal ∧ IsOpen (N : Set G) ∧
      (∀ (g v : Fin n → G), (∀ i, v i ∈ N) → c (g * v) = c g) ∧
      ∀ g, ∀ a ∈ N, M.rho a (c g) = c g := by sorry
