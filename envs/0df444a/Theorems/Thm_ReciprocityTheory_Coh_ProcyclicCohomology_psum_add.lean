-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_psum_add
-- name    : ReciprocityTheory.Coh.ProcyclicCohomology.psum_add
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:50:47.015851+00:00
-- url     : https://prove2.me/theorems/e61e6659-80f6-45d4-bc2b-d3b9e719c6d9
-- title:
--   Procyclic Cohomology: psum add
-- statement:
--   The Procyclic Cohomology construction uses the psum add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ModelComparisonDegreeZeroBijective.lean#L83-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ModelComparisonDegreeZeroBijective.lean#L83-L85

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
open ReciprocityTheory.Gal Topology
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem ReciprocityTheory.Coh.ProcyclicCohomology.psum_add (M : TRep R G) (s : G) (m : M.V) (i j : ℕ) :
    psum M s m (i + j) = psum M s m i + M.rho (s ^ i) (psum M s m j) := by sorry
