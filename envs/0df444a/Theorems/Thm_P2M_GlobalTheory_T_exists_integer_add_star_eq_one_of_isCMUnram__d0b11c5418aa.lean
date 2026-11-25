-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_integer_add_star_eq_one_of_isCMUnram__d0b11c5418aa
-- name    : P2M_GlobalTheory_T_exists_integer_add_star_eq_one_of_isCMUnram__d0b11c5418aa
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:47:57.881873+00:00
-- url     : https://prove2.me/theorems/6b1f3434-7d42-57cd-bffb-d30b524694c6
-- title:
--   P2 M Global Theory T exists integer add star eq one of is CMUnram  d0b11c5418aa: P2 M Global Theory T exists integer add star eq one of is CMUnram  d0b11c5418aa
-- statement:
--   The P2 M Global Theory T exists integer add star eq one of is CMUnram  d0b11c5418aa construction uses the P2 M Global Theory T exists integer add star eq one of is CMUnram  d0b11c5418aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsIntegerAddStarEqOneOfIsCMUnramStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsIntegerAddStarEqOneOfIsCMUnramStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnramStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_integer_add_star_eq_one_of_isCMUnram__d0b11c5418aa : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∃ t : 𝓞 K, (t : K) + star (t : K) = 1 := by sorry

alias «GlobalTheory».«T».«exists_integer_add_star_eq_one_of_isCMUnram'» := P2M_GlobalTheory_T_exists_integer_add_star_eq_one_of_isCMUnram__d0b11c5418aa
