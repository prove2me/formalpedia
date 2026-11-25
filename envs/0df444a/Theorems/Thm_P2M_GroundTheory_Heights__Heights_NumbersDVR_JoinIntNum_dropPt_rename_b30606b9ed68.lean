-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_dropPt_rename_b30606b9ed68
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_dropPt_rename_b30606b9ed68
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:07:36.558296+00:00
-- url     : https://prove2.me/theorems/546574b3-9808-4e9e-b777-4d4099418de7
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num drop Pt rename b30606b9ed68: P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num drop Pt rename b30606b9ed68
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num drop Pt rename b30606b9ed68 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num drop Pt rename b30606b9ed68 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinIntNum.lean#L47-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinIntNum.lean#L47-L53

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_dropPt_rename_b30606b9ed68 (f : MRing ι F) :
    aeval (dropPt F) (rename (liftVar (ι := ι) ptIdx) f) = f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinIntNum».«dropPt_rename» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_dropPt_rename_b30606b9ed68
