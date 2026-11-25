-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_exists_dominant_sub_smul_52005d976b5b
-- name    : P2M_GroundTheory_Heights__Heights_TheoremB_exists_dominant_sub_smul_52005d976b5b
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:41:01.474818+00:00
-- url     : https://prove2.me/theorems/31d7cbe6-7a8e-55b3-8209-bb1287d32097
-- title:
--   P2 M Ground Theory Heights  Heights Theorem B exists dominant sub smul 52005d976b5b: P2 M Ground Theory Heights  Heights Theorem B exists dominant sub smul 52005d976b5b
-- statement:
--   The P2 M Ground Theory Heights  Heights Theorem B exists dominant sub smul 52005d976b5b construction uses the P2 M Ground Theory Heights  Heights Theorem B exists dominant sub smul 52005d976b5b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/ExistsDominantSubSmul.lean#L11-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/ExistsDominantSubSmul.lean#L11-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_StatementsEnd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_ExistsDominantSubSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Filter Topology

theorem P2M_GroundTheory_Heights__Heights_TheoremB_exists_dominant_sub_smul_52005d976b5b (d : IndexData) (u w : Idx d → ℚ) (hu : IsRegular d (uR d u)) :
    ∃ s1 : ℝ, 0 < s1 ∧ ∀ s : ℚ, 0 < s → (s : ℝ) ≤ s1 → IsDominant d (uR d (u - s • w)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TheoremB».«exists_dominant_sub_smul» := P2M_GroundTheory_Heights__Heights_TheoremB_exists_dominant_sub_smul_52005d976b5b
