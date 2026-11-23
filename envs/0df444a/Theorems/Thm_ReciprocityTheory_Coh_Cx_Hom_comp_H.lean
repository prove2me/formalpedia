-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_comp_H
-- name    : ReciprocityTheory.Coh.Cx.Hom.comp_H
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:08:57.826296+00:00
-- url     : https://prove2.me/theorems/de2cea8f-5918-43d5-9d56-d8f310f0bc9a
-- title:
--   Hom: comp H
-- statement:
--   The Hom construction uses the comp H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/DEqZeroOfMemB.lean#L107-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/DEqZeroOfMemB.lean#L107-L110

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

theorem ReciprocityTheory.Coh.Cx.Hom.comp_H (ψ : Hom B C) (φ : Hom A B) (n : ℕ) : (ψ.comp φ).H n = (ψ.H n).comp (φ.H n) := by sorry
