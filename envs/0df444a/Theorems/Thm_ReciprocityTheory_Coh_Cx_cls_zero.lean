-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_zero
-- name    : ReciprocityTheory.Coh.Cx.cls_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:09:12.926129+00:00
-- url     : https://prove2.me/theorems/72c2b7bb-7ca9-45cd-82e6-dddeab9c0eda
-- title:
--   Cx: cls zero
-- statement:
--   The Cx construction uses the cls zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/DEqZeroOfMemB.lean#L38-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/DEqZeroOfMemB.lean#L38-L38

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

theorem ReciprocityTheory.Coh.Cx.cls_zero (n : ℕ) (h : A.d n 0 = 0) : A.cls n 0 h = 0 := by sorry

attribute [defeq] ReciprocityTheory.Coh.Cx.cls_zero
