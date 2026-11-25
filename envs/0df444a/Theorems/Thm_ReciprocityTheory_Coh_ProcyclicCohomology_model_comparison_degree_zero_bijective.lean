-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_model_comparison_degree_zero_bijective
-- name    : ReciprocityTheory.Coh.ProcyclicCohomology.model_comparison_degree_zero_bijective
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:51:39.652783+00:00
-- url     : https://prove2.me/theorems/2e5c8c5a-ab81-5fc1-896b-e3ec00a456aa
-- title:
--   Procyclic Cohomology: model comparison degree zero bijective
-- statement:
--   The Procyclic Cohomology construction uses the model comparison degree zero bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ModelComparisonDegreeZeroBijective.lean#L163-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ModelComparisonDegreeZeroBijective.lean#L163-L194

import Definitions.Def_ReciprocityTheory_GroupCohomology_MemZpowersQuot
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
import Definitions.Def_ReciprocityTheory_GroupCohomology_ModelComparisonDegreeZeroBijective
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
open ReciprocityTheory.Gal Function
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem ReciprocityTheory.Coh.ProcyclicCohomology.model_comparison_degree_zero_bijective [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V] {s : G}
    (hc : ∀ a b : G, a * b = b * a) (hs : Dense (Subgroup.zpowers s : Set G))
    (hidx : ∀ k : ℕ, 0 < k → ∃ W : Subgroup G, IsOpen (W : Set G) ∧ W.index = k)
    (htor : ∀ m : M.V, ∃ k : ℕ, 0 < k ∧ k • m = 0) :
    ∃ e : H1 M.rho ≃ₗ[R] M.V ⧸ LinearMap.range (M.rho s - LinearMap.id),
      ∀ c : Z1 M.rho, e (Submodule.Quotient.mk c) = Submodule.Quotient.mk (c.1 s) := by sorry
