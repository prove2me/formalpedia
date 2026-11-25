-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_comm_of_dense
-- name    : ReciprocityTheory.Coh.ProcyclicCohomology.comm_of_dense
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:50:24.771453+00:00
-- url     : https://prove2.me/theorems/c921e4d7-35d6-41d3-8dcb-d465e00f714b
-- title:
--   Procyclic Cohomology: comm of dense
-- statement:
--   The Procyclic Cohomology construction uses the comm of dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/MemZpowersQuot.lean#L12-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/MemZpowersQuot.lean#L12-L25

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

theorem ReciprocityTheory.Coh.ProcyclicCohomology.comm_of_dense [T2Space G] {s : G} (hs : Dense (Subgroup.zpowers s : Set G)) (a b : G) :
    a * b = b * a := by sorry
