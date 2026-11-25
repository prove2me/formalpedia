-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_congr_on_support_d17f7ce7c14d
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_congr_on_support_d17f7ce7c14d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:10:10.359019+00:00
-- url     : https://prove2.me/theorems/f2739816-e596-41e6-9bdf-d760d2782b2c
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval congr on support d17f7ce7c14d: P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval congr on support d17f7ce7c14d
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval congr on support d17f7ce7c14d construction uses the P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval congr on support d17f7ce7c14d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CycEvalCongrOnSupport.lean#L32-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CycEvalCongrOnSupport.lean#L32-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BlowUpPushHypothesesExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CycEvalCongrOnSupport
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
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {R : Type*} [CommRing R]
omit [Fintype K] [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_congr_on_support_d17f7ce7c14d {n n' : Ideal (MRing ι R) → ℤ} (Z : Ideal (MRing ι R) → ℤ)
    (h : ∀ W, Z W ≠ 0 → n W = n' W) : cycEval n Z = cycEval n' Z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«cycEval_congr_on_support» := P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_congr_on_support_d17f7ce7c14d
