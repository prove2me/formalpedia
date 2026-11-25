-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_subsingleton_H2_of_procyclic_of_torsion
-- name    : ReciprocityTheory.Coh.ProcyclicCohomology.subsingleton_H2_of_procyclic_of_torsion
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:51:24.649092+00:00
-- url     : https://prove2.me/theorems/f48a90c1-399f-5e7b-bcac-2154ae489dad
-- title:
--   Procyclic Cohomology: subsingleton H2 of procyclic of torsion
-- statement:
--   The Procyclic Cohomology construction uses the subsingleton H2 of procyclic of torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/MemCoboundariesOfCocycleProcyclic.lean#L152-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/MemCoboundariesOfCocycleProcyclic.lean#L152-L161

import Definitions.Def_ReciprocityTheory_GroupCohomology_ModelComparisonDegreeZeroBijective
import Definitions.Def_ReciprocityTheory_GroupCohomology_MemCoboundariesOfCocycleProcyclic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Coh.ProcyclicCohomology
open ReciprocityTheory.Gal Topology Function
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem ReciprocityTheory.Coh.ProcyclicCohomology.subsingleton_H2_of_procyclic_of_torsion [CompactSpace G] [TotallyDisconnectedSpace G] (M : TRep R G)
    [DiscreteTopology M.V] {s : G}
    (hc : ∀ a b : G, a * b = b * a) (hs : Dense (Subgroup.zpowers s : Set G))
    (hidx : ∀ k : ℕ, 0 < k → ∃ W : Subgroup G, IsOpen (W : Set G) ∧ W.index = k)
    (htor : ∀ m : M.V, ∃ k : ℕ, 0 < k ∧ k • m = 0) : Subsingleton (H2 M.rho) := by sorry
