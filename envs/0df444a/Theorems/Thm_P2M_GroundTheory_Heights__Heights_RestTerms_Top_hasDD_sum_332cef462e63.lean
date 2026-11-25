-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_sum_332cef462e63
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_sum_332cef462e63
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:43.506853+00:00
-- url     : https://prove2.me/theorems/2f11e114-4b24-47cc-b227-0f74754fac5b
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top has DD sum 332cef462e63: P2 M Ground Theory Heights  Heights Rest Terms Top has DD sum 332cef462e63
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top has DD sum 332cef462e63 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top has DD sum 332cef462e63 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L77-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L77-L85

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
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
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_sum_332cef462e63 {ι : Type*} (s : Finset ι) {f N : ℕ} {H P : ι → RootRing f N}
    (h : ∀ i ∈ s, HasDD f N (H i) (P i)) : HasDD f N (∑ i ∈ s, H i) (∑ i ∈ s, P i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«hasDD_sum» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_sum_332cef462e63
