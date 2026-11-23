-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_cx_smul_d
-- name    : ReciprocityTheory.Coh.cx_smul_d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:17.433782+00:00
-- url     : https://prove2.me/theorems/dd3e5c3d-c800-49be-bc7f-0b8bd59546d0
-- title:
--   Coh: cx smul d
-- statement:
--   The Coh construction uses the cx smul d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/LocaliseA.lean#L14-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/LocaliseA.lean#L14-L14

import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_LocaliseA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open Cx Function
universe u
variable {R : Type u} [CommRing R] {A B : Cx R}

theorem ReciprocityTheory.Coh.cx_smul_d {n : ℕ} (t : R) (x : B.X n) : B.d n (t • x) = t • B.d n x := by sorry
