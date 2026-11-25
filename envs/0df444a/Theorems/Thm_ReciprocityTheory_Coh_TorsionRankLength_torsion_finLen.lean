-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_TorsionRankLength_torsion_finLen
-- name    : ReciprocityTheory.Coh.TorsionRankLength.torsion_finLen
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:50:24.966153+00:00
-- url     : https://prove2.me/theorems/ee189625-d74b-5503-8067-3b41b93a41bb
-- title:
--   Torsion Rank Length: torsion fin Len
-- statement:
--   The Torsion Rank Length construction uses the torsion fin Len property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/RankLenA.lean#L121-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/RankLenA.lean#L121-L129

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
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (H : Type u) [AddCommGroup H] [Module R H] [Module.Finite R H]

theorem ReciprocityTheory.Coh.TorsionRankLength.torsion_finLen : IsFiniteLength R (torsion R H) := by sorry
