-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_finite_quot
-- name    : ReciprocityTheory.Coh.ProcyclicCohomology.finite_quot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:45.083611+00:00
-- url     : https://prove2.me/theorems/ea6412c6-1ab6-4ee8-a994-89ce3c6ebbb8
-- title:
--   Procyclic Cohomology: finite quot
-- statement:
--   The Procyclic Cohomology construction uses the finite quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/MemZpowersQuot.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/MemZpowersQuot.lean#L30-L32

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_MemZpowersQuot
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
open Topology
open scoped Pointwise
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem ReciprocityTheory.Coh.ProcyclicCohomology.finite_quot [CompactSpace G] (hc : ∀ a b : G, a * b = b * a) {W : Subgroup G}
    (hW : IsOpen (W : Set G)) : Finite (G ⧸ W) := by sorry
