-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_tr_add
-- name    : ReciprocityTheory.Coh.ProcyclicCohomology.tr_add
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:51:22.876134+00:00
-- url     : https://prove2.me/theorems/ecb042f6-7610-57a7-927e-2eedac327296
-- title:
--   Procyclic Cohomology: tr add
-- statement:
--   The Procyclic Cohomology construction uses the tr add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/MemCoboundariesOfCocycleProcyclic.lean#L36-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/MemCoboundariesOfCocycleProcyclic.lean#L36-L43

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

theorem ReciprocityTheory.Coh.ProcyclicCohomology.tr_add (M : TRep R G) (f : G × G → M.V) (s : G) (j t : ℕ) :
    tr M f s (j + t) = tr M f s j - ∑ i ∈ Finset.range t, f (s ^ (j + i), s) := by sorry
