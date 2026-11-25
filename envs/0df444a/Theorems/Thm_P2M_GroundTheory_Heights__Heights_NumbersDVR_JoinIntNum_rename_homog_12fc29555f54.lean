-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_rename_homog_12fc29555f54
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_rename_homog_12fc29555f54
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:08:20.095223+00:00
-- url     : https://prove2.me/theorems/4799e743-5c9c-422e-bff1-dcd7a81a8f77
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num rename homog 12fc29555f54: P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num rename homog 12fc29555f54
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num rename homog 12fc29555f54 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num rename homog 12fc29555f54 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinIntNum.lean#L142-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinIntNum.lean#L142-L154

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_rename_homog_12fc29555f54 {f : MRing ι F} {m : K → ℕ}
    (hf : IsWeightedHomogeneous (blockWeight ι) f m) :
    IsWeightedHomogeneous (blockWeight (Sum.elim ι ptIdx))
      (rename (liftVar (ι := ι) ptIdx) f) (extendZero m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinIntNum».«rename_homog» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_rename_homog_12fc29555f54
