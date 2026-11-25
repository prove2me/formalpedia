-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_dropPt_homog_6b1a42b630a2
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_dropPt_homog_6b1a42b630a2
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:07:09.057213+00:00
-- url     : https://prove2.me/theorems/758a188a-3ae9-4d11-9d34-d39f8f34a66a
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num drop Pt homog 6b1a42b630a2: P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num drop Pt homog 6b1a42b630a2
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num drop Pt homog 6b1a42b630a2 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num drop Pt homog 6b1a42b630a2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinIntNum.lean#L156-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinIntNum.lean#L156-L172

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_dropPt_homog_6b1a42b630a2 {g : MRing (Sum.elim ι ptIdx) F} {M : K ⊕ Unit → ℕ}
    (hg : IsWeightedHomogeneous (blockWeight (Sum.elim ι ptIdx)) g M) :
    IsWeightedHomogeneous (blockWeight ι) (aeval (dropPt F) g) (restrictFirst M) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinIntNum».«dropPt_homog» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_dropPt_homog_6b1a42b630a2
