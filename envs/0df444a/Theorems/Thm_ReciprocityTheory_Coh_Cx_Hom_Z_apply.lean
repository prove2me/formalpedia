-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_Z_apply
-- name    : ReciprocityTheory.Coh.Cx.Hom.Z_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:09:19.070805+00:00
-- url     : https://prove2.me/theorems/2d678dbf-fb26-49d6-bfbb-1eeef87083ec
-- title:
--   Hom: Z apply
-- statement:
--   The Hom construction uses the Z apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/DEqZeroOfMemB.lean#L92-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/DEqZeroOfMemB.lean#L92-L92

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

theorem ReciprocityTheory.Coh.Cx.Hom.Z_apply (φ : Hom A B) {n : ℕ} (x : A.Z n) : (φ.Z n x : B.X n) = φ.f n x := by sorry

attribute [defeq] ReciprocityTheory.Coh.Cx.Hom.Z_apply
