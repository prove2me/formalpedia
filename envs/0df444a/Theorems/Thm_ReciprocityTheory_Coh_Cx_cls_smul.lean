-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_smul
-- name    : ReciprocityTheory.Coh.Cx.cls_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:09:40.080511+00:00
-- url     : https://prove2.me/theorems/e50ba3a3-258b-4fd3-94ac-fa81f9071ce3
-- title:
--   Cx: cls smul
-- statement:
--   The Cx construction uses the cls smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/DEqZeroOfMemB.lean#L49-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/DEqZeroOfMemB.lean#L49-L50

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

theorem ReciprocityTheory.Coh.Cx.cls_smul {n : ℕ} (r : R) (x : A.X n) (hx : A.d n x = 0) :
    r • A.cls n x hx = A.cls n (r • x) (d_smul_eq_zero r hx) := by sorry

attribute [defeq] ReciprocityTheory.Coh.Cx.cls_smul
