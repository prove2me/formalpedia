-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_hom_H_smul
-- name    : ReciprocityTheory.Coh.hom_H_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:52:15.814336+00:00
-- url     : https://prove2.me/theorems/cede713e-65c5-46e7-a217-54d94c9bad9c
-- title:
--   Coh: hom H smul
-- statement:
--   The Coh construction uses the hom H smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/FinGen.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/FinGen.lean#L16-L23

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_IsSuccSubset
import Definitions.Def_ReciprocityTheory_GroupCohomology_FinGen
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
variable {R : Type u} [CommRing R]

theorem ReciprocityTheory.Coh.hom_H_smul {A : Cx R} (i : Hom A A) (t : R) (hi : ∀ n x, i.f n x = t • x) (n : ℕ)
    (x : A.H n) : i.H n x = t • x := by sorry
