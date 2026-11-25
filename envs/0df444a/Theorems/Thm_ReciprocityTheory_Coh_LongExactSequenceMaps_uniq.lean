-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_LongExactSequenceMaps_uniq
-- name    : ReciprocityTheory.Coh.LongExactSequenceMaps.uniq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:52:25.517928+00:00
-- url     : https://prove2.me/theorems/bb604a52-3586-45fc-ae2f-32f8ed10093c
-- title:
--   Long Exact Sequence Maps: uniq
-- statement:
--   The Long Exact Sequence Maps construction uses the uniq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ConnNatHolds.lean#L176-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ConnNatHolds.lean#L176-L181

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

theorem ReciprocityTheory.Coh.LongExactSequenceMaps.uniq (hs : SES i p) (δ δ' : ∀ n, C.H n →ₗ[R] A.H (n + 1)) (hδ : IsConn i p δ)
    (hδ' : IsConn i p δ') : δ = δ' := by sorry
