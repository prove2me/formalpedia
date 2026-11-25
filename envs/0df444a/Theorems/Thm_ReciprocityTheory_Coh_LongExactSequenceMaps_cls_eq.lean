-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_LongExactSequenceMaps_cls_eq
-- name    : ReciprocityTheory.Coh.LongExactSequenceMaps.cls_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:51:35.192191+00:00
-- url     : https://prove2.me/theorems/42e02831-7c37-5f8a-97fd-f84f0d6daccc
-- title:
--   Long Exact Sequence Maps: cls eq
-- statement:
--   The Long Exact Sequence Maps construction uses the cls eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ConnNatHolds.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ConnNatHolds.lean#L29-L33

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
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
open ReciprocityTheory.Coh.LongExactSequenceMaps
variable {R : Type u} [CommRing R] {A B C : Cx R}

theorem ReciprocityTheory.Coh.LongExactSequenceMaps.cls_eq (A : Cx R) (n : ℕ) (x y : A.X n) (hx : A.d n x = 0) (hy : A.d n y = 0) :
    A.cls n x hx = A.cls n y hy ↔ x - y ∈ A.B n := by sorry
