-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorLeft_isMultiHomog_rename_assocVar_4a988f335c8a
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorLeft_isMultiHomog_rename_assocVar_4a988f335c8a
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:07:19.955252+00:00
-- url     : https://prove2.me/theorems/6922e720-aa6f-4cec-96d3-fa9cbc0302b4
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Left is Multi Homog rename assoc Var 4a988f335c8a: P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Left is M
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Left is Multi Homog rename assoc Var 4a988f335c8a construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Left is Multi Homog rename assoc Var 4a988f335c8a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinVertDivLeft.lean#L97-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinVertDivLeft.lean#L97-L104

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerLast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinVertDivLeft
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_joinCoord_assocVar_b75e0e1aca5e

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
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (joinCoord mcIdeal mcMap assocDeg assocVar joinCoord_assocVar IsVertDiv)
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisorLeft
variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}
variable [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorLeft_isMultiHomog_rename_assocVar_4a988f335c8a {R : Type} [CommRing R]
    {f : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R} {a : K ⊕ K' → ℕ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (rename (assocVar ι₂) f)
      (Sum.elim (fun k => a (.inl k)) (Sum.elim (fun k => a (.inr k)) 0)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinVerticalDivisorLeft».«isMultiHomog_rename_assocVar» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorLeft_isMultiHomog_rename_assocVar_4a988f335c8a
