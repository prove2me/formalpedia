-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_LongExactSequenceMaps_conn_pS
-- name    : ReciprocityTheory.Coh.LongExactSequenceMaps.conn_pS
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:51:51.610512+00:00
-- url     : https://prove2.me/theorems/cbb8e793-8b1a-5637-8a52-836828231be6
-- title:
--   Long Exact Sequence Maps: conn p S
-- statement:
--   The Long Exact Sequence Maps construction uses the conn p S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ConnNatHolds.lean#L156-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ConnNatHolds.lean#L156-L161

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
noncomputable section
variable {R : Type u} [CommRing R] {A B C : Cx R} (i : Hom A B) (p : Hom B C)

theorem ReciprocityTheory.Coh.LongExactSequenceMaps.conn_pS (hs : SES i p) (n : ℕ) (b : S i n) : conn i p hs n (pS i p hs n b) = θ i p hs n b := by sorry
