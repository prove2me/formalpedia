-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_rename_dropPt_of_homog_e7fc05f7ee1a
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_rename_dropPt_of_homog_e7fc05f7ee1a
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:07:00.392188+00:00
-- url     : https://prove2.me/theorems/9487e493-a93a-4cdc-a6f2-a0b819cedc76
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num rename drop Pt of homog e7fc05f7ee1a: P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num rename drop Pt of homog e7fc05f7ee1a
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num rename drop Pt of homog e7fc05f7ee1a construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num rename drop Pt of homog e7fc05f7ee1a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinIntNum.lean#L117-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinIntNum.lean#L117-L126

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_rename_dropPt_of_homog_e7fc05f7ee1a {g : MRing (Sum.elim ι ptIdx) F} {M : K ⊕ Unit → ℕ}
    (hg : IsWeightedHomogeneous (blockWeight (Sum.elim ι ptIdx)) g M) :
    rename (liftVar (ι := ι) ptIdx) (aeval (dropPt F) g) * X newVar ^ (M (.inr ())) = g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinIntNum».«rename_dropPt_of_homog» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_rename_dropPt_of_homog_e7fc05f7ee1a
