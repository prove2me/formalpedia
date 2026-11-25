-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_finite_blockWeight_eq_7d351ef1e570
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_finite_blockWeight_eq_7d351ef1e570
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:10:39.245289+00:00
-- url     : https://prove2.me/theorems/48986bd8-1763-4423-b586-1e761d63a3e8
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR finite block Weight eq 7d351ef1e570: P2 M Ground Theory Heights  Heights Numbers DVR finite block Weight eq 7d351ef1e570
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR finite block Weight eq 7d351ef1e570 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR finite block Weight eq 7d351ef1e570 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGradedPieceQuot.lean#L11-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGradedPieceQuot.lean#L11-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGradedPieceQuot
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_finite_blockWeight_eq_7d351ef1e570 {K : Type} [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (m : K → ℕ) :
    {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m}.Finite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«finite_blockWeight_eq» := P2M_GroundTheory_Heights__Heights_NumbersDVR_finite_blockWeight_eq_7d351ef1e570
