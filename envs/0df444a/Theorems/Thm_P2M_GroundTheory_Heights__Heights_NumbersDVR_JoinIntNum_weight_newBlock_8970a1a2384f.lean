-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_weight_newBlock_8970a1a2384f
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_weight_newBlock_8970a1a2384f
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:06:31.903593+00:00
-- url     : https://prove2.me/theorems/6180dbe2-8e05-4817-a59a-712a6248b20e
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num weight new Block 8970a1a2384f: P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num weight new Block 8970a1a2384f
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num weight new Block 8970a1a2384f construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num weight new Block 8970a1a2384f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinIntNum.lean#L70-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinIntNum.lean#L70-L83

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_weight_newBlock_8970a1a2384f (d : (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) →₀ ℕ) :
    Finsupp.weight (blockWeight (Sum.elim ι ptIdx)) d (.inr ()) = d newVar := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinIntNum».«weight_newBlock» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_weight_newBlock_8970a1a2384f
