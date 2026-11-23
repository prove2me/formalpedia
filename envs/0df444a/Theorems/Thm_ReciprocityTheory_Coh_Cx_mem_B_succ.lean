-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_Cx_mem_B_succ
-- name    : ReciprocityTheory.Coh.Cx.mem_B_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:09:48.152336+00:00
-- url     : https://prove2.me/theorems/9491d0a7-3cfc-4597-83aa-67bce2281376
-- title:
--   Cx: mem B succ
-- statement:
--   The Cx construction uses the mem B succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/DEqZeroOfMemB.lean#L79-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/DEqZeroOfMemB.lean#L79-L81

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
universe u
open ReciprocityTheory.Coh.Cx
variable {R : Type u} [CommRing R] {A B C : Cx R}

theorem ReciprocityTheory.Coh.Cx.mem_B_succ {n : ℕ} {x : A.X (n + 1)} : x ∈ A.B (n + 1) ↔ ∃ y, A.d n y = x := by sorry
