-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointVerticalDivisor_rename_weightedHomogeneousComponent_6c090a1c8134
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointVerticalDivisor_rename_weightedHomogeneousComponent_6c090a1c8134
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:07:51.436386+00:00
-- url     : https://prove2.me/theorems/38cee49d-0bfc-46fc-a90f-9c0a5bc1177a
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Point Vertical Divisor rename weighted Homogeneous Component 6c090a1c8134: P2 M Ground Theory Heights  Heights Numbers DVR Join Point Vertical Divi
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Point Vertical Divisor rename weighted Homogeneous Component 6c090a1c8134 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Point Vertical Divisor rename weighted Homogeneous Component 6c090a1c8134 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinPointVertDiv.lean#L35-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinPointVertDiv.lean#L35-L54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerExtra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVerticalDivisorJoinPullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinPointVertDiv
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
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord liftVar pullDeg joinCoord mcIdeal IsVertDiv)
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointVerticalDivisor
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
variable [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
omit [Fintype K'] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointVerticalDivisor_rename_weightedHomogeneousComponent_6c090a1c8134 [DecidableEq K] [DecidableEq K'] {R : Type} [CommRing R]
    (b : K → ℕ) (h : MvPolynomial (Σ k, ι k) R) :
    rename (liftVar ι') (weightedHomogeneousComponent (blockWeight ι) b h) =
      weightedHomogeneousComponent (blockWeight (Sum.elim ι ι')) (Sum.elim b 0)
        (rename (liftVar ι') h) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinPointVerticalDivisor».«rename_weightedHomogeneousComponent» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointVerticalDivisor_rename_weightedHomogeneousComponent_6c090a1c8134
