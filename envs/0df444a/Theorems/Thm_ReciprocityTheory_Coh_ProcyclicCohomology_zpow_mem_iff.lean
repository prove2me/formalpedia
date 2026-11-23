-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_zpow_mem_iff
-- name    : ReciprocityTheory.Coh.ProcyclicCohomology.zpow_mem_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:47.236858+00:00
-- url     : https://prove2.me/theorems/ee07555c-c82f-4a1d-983f-c5f87aa94cc5
-- title:
--   Procyclic Cohomology: zpow mem iff
-- statement:
--   The Procyclic Cohomology construction uses the zpow mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/MemZpowersQuot.lean#L52-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/MemZpowersQuot.lean#L52-L61

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
variable {s : G}

theorem ReciprocityTheory.Coh.ProcyclicCohomology.zpow_mem_iff [CompactSpace G] (hc : ∀ a b : G, a * b = b * a)
    (hs : Dense (Subgroup.zpowers s : Set G)) {W : Subgroup G} (hW : IsOpen (W : Set G)) (z : ℤ) :
    s ^ z ∈ W ↔ (W.index : ℤ) ∣ z := by sorry
