-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_mixedDiff_map_ae37bf432065
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_mixedDiff_map_ae37bf432065
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:07:01.977033+00:00
-- url     : https://prove2.me/theorems/783fd867-b32f-4b6a-a9c0-6eee4497dfd9
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num mixed Diff map ae37bf432065: P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num mixed Diff map ae37bf432065
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num mixed Diff map ae37bf432065 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num mixed Diff map ae37bf432065 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinIntNum.lean#L266-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinIntNum.lean#L266-L276

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_mixedDiff_map_ae37bf432065 (V : Ideal (MRing ι F)) {n : ℕ} (bs : Fin n → K → ℤ) (m' : K ⊕ Unit → ℤ) :
    mixedDiff (fun j => pullDeg (K' := Unit) (bs j))
        (hilbFn (V.map (rename (liftVar (ι := ι) ptIdx)))) m' =
      if 0 ≤ m' (.inr ()) then mixedDiff bs (hilbFn V) (fun k => m' (.inl k)) else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinIntNum».«mixedDiff_map» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_mixedDiff_map_ae37bf432065
