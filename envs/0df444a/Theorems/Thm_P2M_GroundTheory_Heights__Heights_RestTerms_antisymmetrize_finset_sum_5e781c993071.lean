-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_antisymmetrize_finset_sum_5e781c993071
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_antisymmetrize_finset_sum_5e781c993071
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:35:50.570148+00:00
-- url     : https://prove2.me/theorems/7c62c062-9432-47f8-9aec-53954084d984
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms antisymmetrize finset sum 5e781c993071: P2 M Ground Theory Heights  Heights Rest Terms antisymmetrize finset sum 5e781c993071
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms antisymmetrize finset sum 5e781c993071 construction uses the P2 M Ground Theory Heights  Heights Rest Terms antisymmetrize finset sum 5e781c993071 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagAntisymDecomposition.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagAntisymDecomposition.lean#L11-L14

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagAntisymDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset

theorem P2M_GroundTheory_Heights__Heights_RestTerms_antisymmetrize_finset_sum_5e781c993071 (f N : ℕ) {ι : Type*} (s : Finset ι) (g : ι → RootRing f N) :
    antisymmetrize f N (∑ i ∈ s, g i) = ∑ i ∈ s, antisymmetrize f N (g i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«antisymmetrize_finset_sum» := P2M_GroundTheory_Heights__Heights_RestTerms_antisymmetrize_finset_sum_5e781c993071
