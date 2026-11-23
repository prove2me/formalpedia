-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_H_cls
-- name    : ReciprocityTheory.Coh.Cx.Hom.H_cls
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:09:37.412671+00:00
-- url     : https://prove2.me/theorems/abb1d54c-42e9-4343-9e5a-4b3c5bd3876f
-- title:
--   Hom: H cls
-- statement:
--   The Hom construction uses the H cls property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/DEqZeroOfMemB.lean#L94-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/DEqZeroOfMemB.lean#L94-L95

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

theorem ReciprocityTheory.Coh.Cx.Hom.H_cls (φ : Hom A B) {n : ℕ} (x : A.X n) (hx : A.d n x = 0) :
    φ.H n (A.cls n x hx) = B.cls n (φ.f n x) (φ.d_f_eq_zero hx) := by sorry

attribute [defeq] ReciprocityTheory.Coh.Cx.Hom.H_cls
