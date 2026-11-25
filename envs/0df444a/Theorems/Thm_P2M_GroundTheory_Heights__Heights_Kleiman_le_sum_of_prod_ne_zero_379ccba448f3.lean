-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_le_sum_of_prod_ne_zero_379ccba448f3
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_le_sum_of_prod_ne_zero_379ccba448f3
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:01:08.240112+00:00
-- url     : https://prove2.me/theorems/bbba957d-ef22-4c90-b1f8-6161719a38a6
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman le sum of prod ne zero 379ccba448f3: P2 M Ground Theory Heights  Heights Kleiman le sum of prod ne zero 379ccba448f3
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman le sum of prod ne zero 379ccba448f3 construction uses the P2 M Ground Theory Heights  Heights Kleiman le sum of prod ne zero 379ccba448f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PSubsetDiffConst.lean#L60-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PSubsetDiffConst.lean#L60-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StSubsetDiffConst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PSubsetDiffConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Kleiman_le_sum_of_prod_ne_zero_379ccba448f3 (n : ℕ) (a : Fin n → ℕ) (h : (∏ i, (1 - (0 : ℚ) ^ a i)) ≠ 0) :
    n ≤ ∑ i, a i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«le_sum_of_prod_ne_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_le_sum_of_prod_ne_zero_379ccba448f3
