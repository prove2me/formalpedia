-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_foldr_diffStep_pullDeg_d8ca0217b33b
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_foldr_diffStep_pullDeg_d8ca0217b33b
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:06:47.464451+00:00
-- url     : https://prove2.me/theorems/4b1a035f-127c-4d45-a019-438a10d2662a
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num foldr diff Step pull Deg d8ca0217b33b: P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num foldr diff Step pull Deg d8ca0217b33b
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num foldr diff Step pull Deg d8ca0217b33b construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num foldr diff Step pull Deg d8ca0217b33b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinIntNum.lean#L246-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinIntNum.lean#L246-L264

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_foldr_diffStep_pullDeg_d8ca0217b33b (L : List (K → ℤ)) (h : (K → ℤ) → ℤ)
    (h' : (K ⊕ Unit → ℤ) → ℤ)
    (hh : ∀ m', h' m' = if 0 ≤ m' (.inr ()) then h (fun k => m' (.inl k)) else 0)
    (m' : K ⊕ Unit → ℤ) :
    (L.map (pullDeg (K' := Unit))).foldr diffStep h' m' =
      if 0 ≤ m' (.inr ()) then L.foldr diffStep h (fun k => m' (.inl k)) else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinIntNum».«foldr_diffStep_pullDeg» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_foldr_diffStep_pullDeg_d8ca0217b33b
