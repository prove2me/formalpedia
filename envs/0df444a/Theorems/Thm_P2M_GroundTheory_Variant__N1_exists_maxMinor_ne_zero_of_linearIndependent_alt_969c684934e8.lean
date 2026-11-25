-- Prove2me | Theorems.Thm_P2M_GroundTheory_Variant__N1_exists_maxMinor_ne_zero_of_linearIndependent_alt_969c684934e8
-- name    : P2M_GroundTheory_Variant__N1_exists_maxMinor_ne_zero_of_linearIndependent_alt_969c684934e8
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:54:44.478806+00:00
-- url     : https://prove2.me/theorems/391af18a-1f20-45b7-8988-ee3c45a13802
-- title:
--   P2 M Ground Theory Variant  N1 exists max Minor ne zero of linear Independent alt 969c684934e8: P2 M Ground Theory Variant  N1 exists max Minor ne zero of linear Independent alt 969c684934e8
-- statement:
--   The P2 M Ground Theory Variant  N1 exists max Minor ne zero of linear Independent alt 969c684934e8 construction uses the P2 M Ground Theory Variant  N1 exists max Minor ne zero of linear Independent alt 969c684934e8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/ExistsMaxMinorNeZeroOfLinearIndependentAlt.lean#L14-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/ExistsMaxMinorNeZeroOfLinearIndependentAlt.lean#L14-L74

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsMaxMinorNeZeroOfLinearIndependentAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Variant₂ GroundTheory.Variant₂.N1

theorem P2M_GroundTheory_Variant__N1_exists_maxMinor_ne_zero_of_linearIndependent_alt_969c684934e8 {R : Type*} [CommRing R] {n k : ℕ}
    [IsDomain R] (B : Matrix (Fin n) (Fin k) R) (hB : LinearIndependent R B.col) :
    ∃ s : KSubset n k, maxMinor B s ≠ 0 := by sorry

alias «GroundTheory».«Variant₂».«N1».«exists_maxMinor_ne_zero_of_linearIndependent_alt» := P2M_GroundTheory_Variant__N1_exists_maxMinor_ne_zero_of_linearIndependent_alt_969c684934e8
