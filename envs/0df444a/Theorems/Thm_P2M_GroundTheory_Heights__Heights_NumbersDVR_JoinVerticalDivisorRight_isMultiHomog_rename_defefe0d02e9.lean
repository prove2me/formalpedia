-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_isMultiHomog_rename_defefe0d02e9
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_isMultiHomog_rename_defefe0d02e9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:43.282111+00:00
-- url     : https://prove2.me/theorems/7d165aac-2304-4a9a-b589-a1ce0a5881e0
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Right is Multi Homog rename defefe0d02e9: P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Right is Multi Hom
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Right is Multi Homog rename defefe0d02e9 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Right is Multi Homog rename defefe0d02e9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinVertDivRight.lean#L71-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinVertDivRight.lean#L71-L80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsMoreAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinVertDivRight
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
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal mcMap joinCoord midDeg midVar)
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisorRight
variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}
variable [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_isMultiHomog_rename_defefe0d02e9 [DecidableEq K] [DecidableEq K'] [DecidableEq K₂] {R : Type} [CommRing R]
    {f : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R} {a : K ⊕ K' → ℕ} (hf : IsMultiHomog f a) :
    IsMultiHomog (rename (midVar ι₂) f) (midNat a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinVerticalDivisorRight».«isMultiHomog_rename» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_isMultiHomog_rename_defefe0d02e9
