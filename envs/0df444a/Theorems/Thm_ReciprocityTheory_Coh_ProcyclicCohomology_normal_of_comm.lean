-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_normal_of_comm
-- name    : ReciprocityTheory.Coh.ProcyclicCohomology.normal_of_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:51.25329+00:00
-- url     : https://prove2.me/theorems/57d20be1-ea63-45be-82a2-83d5b4521ffd
-- title:
--   Procyclic Cohomology: normal of comm
-- statement:
--   The Procyclic Cohomology construction uses the normal of comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/MemZpowersQuot.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/MemZpowersQuot.lean#L27-L28

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

theorem ReciprocityTheory.Coh.ProcyclicCohomology.normal_of_comm (hc : ∀ a b : G, a * b = b * a) (W : Subgroup G) : W.Normal := by sorry
