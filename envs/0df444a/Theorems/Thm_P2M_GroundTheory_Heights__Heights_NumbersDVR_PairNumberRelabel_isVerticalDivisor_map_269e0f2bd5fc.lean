-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_isVerticalDivisor_map_269e0f2bd5fc
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_isVerticalDivisor_map_269e0f2bd5fc
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:03:39.992426+00:00
-- url     : https://prove2.me/theorems/5ac716a0-b450-4ca0-b9c0-e376781d2115
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel is Vertical Divisor map 269e0f2bd5fc: P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel is Vertical Divisor map 26
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel is Vertical Divisor map 269e0f2bd5fc construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel is Vertical Divisor map 269e0f2bd5fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean#L226-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean#L226-L264

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_IntNumRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberRelabel
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
open GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberRelabel
variable {K₁ K₂ : Type} [DecidableEq K₁] [DecidableEq K₂] {ι₁ : K₁ → Type} {ι₂ : K₂ → Type}
  {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k))
omit [IsDomain O] [IsDiscreteValuationRing O]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_isVerticalDivisor_map_269e0f2bd5fc (hσ : ∀ v, (σ v).1 = e v.1) (P : Ideal (MRing ι₁ O)) (ϖ : O)
    (b : K₂ → ℤ) (f g : MRing ι₁ O) (h : IsVerticalDivisor P ϖ (b ∘ e) f g) :
    IsVerticalDivisor (P.map (ren (R := O) σ : MRing ι₁ O →+* MRing ι₂ O)) ϖ b (rename σ f)
      (rename σ g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«PairNumberRelabel».«isVerticalDivisor_map» := P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_isVerticalDivisor_map_269e0f2bd5fc
