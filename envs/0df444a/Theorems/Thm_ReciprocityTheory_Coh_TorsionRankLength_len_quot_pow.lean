-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_TorsionRankLength_len_quot_pow
-- name    : ReciprocityTheory.Coh.TorsionRankLength.len_quot_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:44.42793+00:00
-- url     : https://prove2.me/theorems/b1bf58bf-ae80-4993-a2f1-0fbd0ce24104
-- title:
--   Torsion Rank Length: len quot pow
-- statement:
--   The Torsion Rank Length construction uses the len quot pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/RankLenA.lean#L54-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/RankLenA.lean#L54-L117

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

theorem ReciprocityTheory.Coh.TorsionRankLength.len_quot_pow {t : R} (ht : Irreducible t) (k : ℕ) :
    Module.length R (R ⧸ Ideal.span {t ^ k}) = k := by sorry
