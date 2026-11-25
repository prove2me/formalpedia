-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_rename_dropPt_monomial_0fae10bf47d2
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_rename_dropPt_monomial_0fae10bf47d2
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:06:51.97112+00:00
-- url     : https://prove2.me/theorems/9b7966c3-690f-4c37-afd0-2f11e0893060
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num rename drop Pt monomial 0fae10bf47d2: P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num rename drop Pt monomial 0fae10bf47d2
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num rename drop Pt monomial 0fae10bf47d2 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num rename drop Pt monomial 0fae10bf47d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinIntNum.lean#L85-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinIntNum.lean#L85-L115

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_rename_dropPt_monomial_0fae10bf47d2 (d : (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) →₀ ℕ) (c : F) :
    rename (liftVar (ι := ι) ptIdx) (aeval (dropPt F) (monomial d c)) * X newVar ^ (d newVar) =
      monomial d c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinIntNum».«rename_dropPt_monomial» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_rename_dropPt_monomial_0fae10bf47d2
