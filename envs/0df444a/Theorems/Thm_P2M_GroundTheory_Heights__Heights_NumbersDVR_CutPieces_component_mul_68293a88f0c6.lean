-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_CutPieces_component_mul_68293a88f0c6
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_CutPieces_component_mul_68293a88f0c6
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:29:40.047182+00:00
-- url     : https://prove2.me/theorems/10770b00-838e-4b23-84c4-b689c13d3b42
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Cut Pieces component mul 68293a88f0c6: P2 M Ground Theory Heights  Heights Numbers DVR Cut Pieces component mul 68293a88f0c6
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Cut Pieces component mul 68293a88f0c6 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Cut Pieces component mul 68293a88f0c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PCutPieces.lean#L38-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PCutPieces.lean#L38-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutPieces
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
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.CutPieces
variable {F : Type*} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open Classical

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_CutPieces_component_mul_68293a88f0c6 {x : MRing ι F} {e : K → ℕ} (hx : IsMultiHomog x e) (y : MRing ι F)
    (m : K → ℕ) :
    weightedHomogeneousComponent (blockWeight ι) m (x * y) =
      if e ≤ m then x * weightedHomogeneousComponent (blockWeight ι) (m - e) y else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«CutPieces».«component_mul» := P2M_GroundTheory_Heights__Heights_NumbersDVR_CutPieces_component_mul_68293a88f0c6
