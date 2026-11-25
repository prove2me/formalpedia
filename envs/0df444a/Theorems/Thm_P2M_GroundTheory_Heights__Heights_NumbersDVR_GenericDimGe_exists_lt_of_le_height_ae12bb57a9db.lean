-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericDimGe_exists_lt_of_le_height_ae12bb57a9db
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericDimGe_exists_lt_of_le_height_ae12bb57a9db
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:07:31.357799+00:00
-- url     : https://prove2.me/theorems/1a6f501b-ebcc-42ab-983b-2c8c34d8df87
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Generic Dim Ge exists lt of le height ae12bb57a9db: P2 M Ground Theory Heights  Heights Numbers DVR Generic Dim Ge exists lt of le height ae12bb57a9db
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Generic Dim Ge exists lt of le height ae12bb57a9db construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Generic Dim Ge exists lt of le height ae12bb57a9db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericDimGe.lean#L104-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericDimGe.lean#L104-L111

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericDimGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericDimGe
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
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.GenericDimGe

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericDimGe_exists_lt_of_le_height_ae12bb57a9db {α : Type*} [Preorder α] {a : α} {n : ℕ}
    (h : ((n + 1 : ℕ) : ℕ∞) ≤ Order.height a) : ∃ b < a, (n : ℕ∞) ≤ Order.height b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«GenericDimGe».«exists_lt_of_le_height» := P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericDimGe_exists_lt_of_le_height_ae12bb57a9db
