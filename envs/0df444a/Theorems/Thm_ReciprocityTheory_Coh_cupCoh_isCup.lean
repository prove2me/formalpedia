-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_cupCoh_isCup
-- name    : ReciprocityTheory.Coh.cupCoh_isCup
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:51:20.470156+00:00
-- url     : https://prove2.me/theorems/40e45243-7b15-5add-919a-ebb3bcb4ce65
-- title:
--   Coh: cup Coh is Cup
-- statement:
--   The Coh construction uses the cup Coh is Cup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ContractNthCastAddCastSucc.lean#L216-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ContractNthCastAddCastSucc.lean#L216-L218

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ContractNthCastAddCastSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal
noncomputable section
universe u
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem ReciprocityTheory.Coh.cupCoh_isCup {M N P : TRep R G} (b : Pairing M N P) : IsCup b (cupCoh b) := by sorry
