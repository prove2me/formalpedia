-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_neg
-- name    : ReciprocityTheory.Coh.Cx.cls_neg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:09:44.132391+00:00
-- url     : https://prove2.me/theorems/a3f85186-607f-4739-be6e-e25e9db3d499
-- title:
--   Cx: cls neg
-- statement:
--   The Cx construction uses the cls neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/DEqZeroOfMemB.lean#L46-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/DEqZeroOfMemB.lean#L46-L47

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

theorem ReciprocityTheory.Coh.Cx.cls_neg {n : ℕ} (x : A.X n) (hx : A.d n x = 0) :
    -A.cls n x hx = A.cls n (-x) (d_neg_eq_zero hx) := by sorry

attribute [defeq] ReciprocityTheory.Coh.Cx.cls_neg
