-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_homogSubmodule_eq_map_937d9ae32e0e
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_homogSubmodule_eq_map_937d9ae32e0e
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:06:49.932174+00:00
-- url     : https://prove2.me/theorems/c8e97816-9e92-4f37-a3df-661388943d42
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num homog Submodule eq map 937d9ae32e0e: P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num homog Submodule eq map 937d9ae32e0e
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num homog Submodule eq map 937d9ae32e0e construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num homog Submodule eq map 937d9ae32e0e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinIntNum.lean#L174-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinIntNum.lean#L174-L198

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_homogSubmodule_eq_map_937d9ae32e0e (M : K ⊕ Unit → ℕ) :
    weightedHomogeneousSubmodule F (blockWeight (Sum.elim ι ptIdx)) M =
      (weightedHomogeneousSubmodule F (blockWeight ι) (restrictFirst M)).map
        ((LinearMap.mulRight F (X newVar ^ M (.inr ()))).comp
          (rename (liftVar (ι := ι) ptIdx)).toLinearMap) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinIntNum».«homogSubmodule_eq_map» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_homogSubmodule_eq_map_937d9ae32e0e
