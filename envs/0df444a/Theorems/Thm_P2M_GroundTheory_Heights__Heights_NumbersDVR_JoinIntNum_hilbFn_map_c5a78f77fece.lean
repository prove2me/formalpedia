-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_hilbFn_map_c5a78f77fece
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_hilbFn_map_c5a78f77fece
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:06:35.593334+00:00
-- url     : https://prove2.me/theorems/19733083-439b-43a6-b0da-172ccefeb38b
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num hilb Fn map c5a78f77fece: P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num hilb Fn map c5a78f77fece
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num hilb Fn map c5a78f77fece construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num hilb Fn map c5a78f77fece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinIntNum.lean#L228-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinIntNum.lean#L228-L244

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_hilbFn_map_c5a78f77fece (V : Ideal (MRing ι F)) (m' : K ⊕ Unit → ℤ) :
    hilbFn (V.map (rename (liftVar (ι := ι) ptIdx))) m' =
      if 0 ≤ m' (.inr ()) then hilbFn V (fun k => m' (.inl k)) else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinIntNum».«hilbFn_map» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_hilbFn_map_c5a78f77fece
