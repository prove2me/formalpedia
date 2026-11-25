-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_finite_setOf_weight_blockWeight_eq_d003e8a029f8
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_finite_setOf_weight_blockWeight_eq_d003e8a029f8
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:10:39.751016+00:00
-- url     : https://prove2.me/theorems/f8fe66c9-b1a6-4cdd-bd59-4b093c9808b2
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR finite set Of weight block Weight eq d003e8a029f8: P2 M Ground Theory Heights  Heights Numbers DVR finite set Of weight block Weight eq d003e8a029f8
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR finite set Of weight block Weight eq d003e8a029f8 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR finite set Of weight block Weight eq d003e8a029f8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGradedPieceFree.lean#L11-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGradedPieceFree.lean#L11-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGradedPieceFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_finite_setOf_weight_blockWeight_eq_d003e8a029f8 {K : Type} [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (m : K → ℕ) :
    {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m}.Finite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«finite_setOf_weight_blockWeight_eq» := P2M_GroundTheory_Heights__Heights_NumbersDVR_finite_setOf_weight_blockWeight_eq_d003e8a029f8
