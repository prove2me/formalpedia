-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_hilbFn_top_c8e6fde21a27
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_hilbFn_top_c8e6fde21a27
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:10:21.452353+00:00
-- url     : https://prove2.me/theorems/d571f9b5-a16f-4e2f-93a4-c7a2f4852d0b
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR hilb Fn top c8e6fde21a27: P2 M Ground Theory Heights  Heights Numbers DVR hilb Fn top c8e6fde21a27
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR hilb Fn top c8e6fde21a27 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR hilb Fn top c8e6fde21a27 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsCN.lean#L300-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsCN.lean#L300-L307

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_hilbFn_top_c8e6fde21a27 {F : Type*} [Field F] {K : Type*} [DecidableEq K] {ι : K → Type*}
    (m : K → ℤ) : hilbFn (⊤ : Ideal (MRing ι F)) m = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«hilbFn_top» := P2M_GroundTheory_Heights__Heights_NumbersDVR_hilbFn_top_c8e6fde21a27
