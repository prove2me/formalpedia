-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_weight_mapDomain_f5b33ab6271c
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_weight_mapDomain_f5b33ab6271c
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:17:35.45221+00:00
-- url     : https://prove2.me/theorems/56da1a74-1e91-4a98-8389-ca397e2efb0a
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Relabel weight map Domain f5b33ab6271c: P2 M Ground Theory Heights  Heights Field Numbers Relabel weight map Domain f5b33ab6271c
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Relabel weight map Domain f5b33ab6271c construction uses the P2 M Ground Theory Heights  Heights Field Numbers Relabel weight map Domain f5b33ab6271c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/IntNumRelabel.lean#L76-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/IntNumRelabel.lean#L76-L88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_IntNumRelabel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
open GroundTheory.Heights₂.Heights.FieldNumbers.Relabel
variable {K₁ K₂ : Type*} [DecidableEq K₁] [DecidableEq K₂] {ι₁ : K₁ → Type*} {ι₂ : K₂ → Type*}
  (e : K₁ ≃ K₂) (φ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hφ : ∀ v, (φ v).1 = e v.1)
  {F : Type*} [Field F]
include hφ

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_weight_mapDomain_f5b33ab6271c (d : (Σ k, ι₁ k) →₀ ℕ) :
    Finsupp.weight (blockWeight ι₂) (Finsupp.mapDomain φ d) =
      Finsupp.weight (blockWeight ι₁) d ∘ e.symm := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«Relabel».«weight_mapDomain» := P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_weight_mapDomain_f5b33ab6271c
