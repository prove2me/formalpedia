-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_stab_isOpen
-- name    : ReciprocityTheory.Coh.ProcyclicCohomology.stab_isOpen
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:51:58.509415+00:00
-- url     : https://prove2.me/theorems/eca5a04c-9403-494c-af89-f9821adbdc85
-- title:
--   Procyclic Cohomology: stab is Open
-- statement:
--   The Procyclic Cohomology construction uses the stab is Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ModelComparisonDegreeZeroBijective.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ModelComparisonDegreeZeroBijective.lean#L26-L27

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

theorem ReciprocityTheory.Coh.ProcyclicCohomology.stab_isOpen (M : TRep R G) [DiscreteTopology M.V] (m : M.V) : IsOpen (stab M m : Set G) := by sorry
