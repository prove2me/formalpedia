-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_LongExactSequenceMaps_les_of
-- name    : ReciprocityTheory.Coh.LongExactSequenceMaps.les_of
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:51:57.295962+00:00
-- url     : https://prove2.me/theorems/6bec8568-bf5b-5204-87c3-2e578132c92a
-- title:
--   Long Exact Sequence Maps: les of
-- statement:
--   The Long Exact Sequence Maps construction uses the les of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ConnNatHolds.lean#L183-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ConnNatHolds.lean#L183-L249

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
variable {R : Type u} [CommRing R] {A B C : Cx R} (i : Hom A B) (p : Hom B C)

theorem ReciprocityTheory.Coh.LongExactSequenceMaps.les_of (hs : SES i p) (δ : ∀ n, C.H n →ₗ[R] A.H (n + 1)) (hδ : IsConn i p δ) :
    LES i p δ := by sorry
