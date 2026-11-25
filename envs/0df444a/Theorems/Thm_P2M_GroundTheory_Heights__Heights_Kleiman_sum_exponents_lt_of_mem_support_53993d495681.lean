-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_sum_exponents_lt_of_mem_support_53993d495681
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_sum_exponents_lt_of_mem_support_53993d495681
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:01:42.190103+00:00
-- url     : https://prove2.me/theorems/b40f6736-04f5-4287-bcdf-4c4551fb0d0e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman sum exponents lt of mem support 53993d495681: P2 M Ground Theory Heights  Heights Kleiman sum exponents lt of mem support 53993d495681
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman sum exponents lt of mem support 53993d495681 construction uses the P2 M Ground Theory Heights  Heights Kleiman sum exponents lt of mem support 53993d495681 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PSubsetDiffConst.lean#L52-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PSubsetDiffConst.lean#L52-L58

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_sum_exponents_lt_of_mem_support_53993d495681 {σ : Type*} [Fintype σ] {Q : MvPolynomial σ ℚ} {D : ℕ}
    (h : Q = 0 ∨ Q.totalDegree < D) {e : σ →₀ ℕ} (he : e ∈ Q.support) : ∑ j, e j < D := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«sum_exponents_lt_of_mem_support» := P2M_GroundTheory_Heights__Heights_Kleiman_sum_exponents_lt_of_mem_support_53993d495681
