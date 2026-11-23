-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_per_mul
-- name    : ReciprocityTheory.Coh.ProcyclicCohomology.per_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:59.351716+00:00
-- url     : https://prove2.me/theorems/c554a47d-de3b-430b-aeb1-d3ddb25d7f55
-- title:
--   Procyclic Cohomology: per mul
-- statement:
--   The Procyclic Cohomology construction uses the per mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/MemZpowersQuot.lean#L89-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/MemZpowersQuot.lean#L89-L92

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
variable {X : Type*} (n : ℕ) (T : ℕ → X)

theorem ReciprocityTheory.Coh.ProcyclicCohomology.per_mul (hper : ∀ j, T (j + n) = T j) (a t : ℕ) : T (a + n * t) = T a := by sorry
