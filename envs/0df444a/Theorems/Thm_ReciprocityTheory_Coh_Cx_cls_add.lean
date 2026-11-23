-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_add
-- name    : ReciprocityTheory.Coh.Cx.cls_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:08:47.026905+00:00
-- url     : https://prove2.me/theorems/0147433e-1c27-4f8f-93aa-c81429c2c52a
-- title:
--   Cx: cls add
-- statement:
--   The Cx construction uses the cls add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/DEqZeroOfMemB.lean#L40-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/DEqZeroOfMemB.lean#L40-L41

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

theorem ReciprocityTheory.Coh.Cx.cls_add {n : ℕ} (x y : A.X n) (hx : A.d n x = 0) (hy : A.d n y = 0) :
    A.cls n x hx + A.cls n y hy = A.cls n (x + y) (d_add_eq_zero hx hy) := by sorry

attribute [defeq] ReciprocityTheory.Coh.Cx.cls_add
