-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_TorsionRankLength_mem_K
-- name    : ReciprocityTheory.Coh.TorsionRankLength.mem_K
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:50:49.875319+00:00
-- url     : https://prove2.me/theorems/8895d014-06f4-4933-9e45-ecfebc0624ad
-- title:
--   Torsion Rank Length: mem K
-- statement:
--   The Torsion Rank Length construction uses the mem K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/RankLenA.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/RankLenA.lean#L17-L18

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_RankLenA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.TorsionRankLength
universe u
open Module Submodule Function
open scoped Pointwise TensorProduct
variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]

theorem ReciprocityTheory.Coh.TorsionRankLength.mem_K {r : R} {x : M} : x ∈ K M r ↔ r • x = 0 := by sorry
