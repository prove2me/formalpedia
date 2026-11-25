-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_comp_H_apply
-- name    : ReciprocityTheory.Coh.Cx.Hom.comp_H_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:27:32.6538+00:00
-- url     : https://prove2.me/theorems/1c48c9a8-0abd-53ba-9624-f79c647d86a4
-- title:
--   Hom: comp H apply
-- statement:
--   The Hom construction uses the comp H apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/DEqZeroOfMemB.lean#L112-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/DEqZeroOfMemB.lean#L112-L115

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

theorem ReciprocityTheory.Coh.Cx.Hom.comp_H_apply (ψ : Hom B C) (φ : Hom A B) (n : ℕ) (c : A.H n) :
    (ψ.comp φ).H n c = ψ.H n (φ.H n c) := by sorry
