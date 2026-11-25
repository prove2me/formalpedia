-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_mul_pow_mem_map_iff_e06cc1491dc2
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_mul_pow_mem_map_iff_e06cc1491dc2
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:07:53.372184+00:00
-- url     : https://prove2.me/theorems/aef03f7a-7258-41a0-8916-cca4ba5abb59
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num mul pow mem map iff e06cc1491dc2: P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num mul pow mem map iff e06cc1491dc2
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num mul pow mem map iff e06cc1491dc2 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num mul pow mem map iff e06cc1491dc2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinIntNum.lean#L55-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinIntNum.lean#L55-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinIntNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PEventualValueFacts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinIntNum
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
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx liftVar pullDeg)
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
noncomputable section
set_option linter.unusedSectionVars false
variable {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_mul_pow_mem_map_iff_e06cc1491dc2 (V : Ideal (MRing ι F)) (f : MRing ι F) (t : ℕ) :
    rename (liftVar (ι := ι) ptIdx) f * X newVar ^ t ∈ V.map (rename (liftVar (ι := ι) ptIdx)) ↔
      f ∈ V := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinIntNum».«mul_pow_mem_map_iff» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_mul_pow_mem_map_iff_e06cc1491dc2
