-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_hilbFn_map_rename_19bfaf389bfb
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_hilbFn_map_rename_19bfaf389bfb
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:02.054339+00:00
-- url     : https://prove2.me/theorems/e196da24-efce-4764-8e1e-95a2f23d1685
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Relabel hilb Fn map rename 19bfaf389bfb: P2 M Ground Theory Heights  Heights Field Numbers Relabel hilb Fn map rename 19bfaf389bfb
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Relabel hilb Fn map rename 19bfaf389bfb construction uses the P2 M Ground Theory Heights  Heights Field Numbers Relabel hilb Fn map rename 19bfaf389bfb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/IntNumRelabel.lean#L126-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/IntNumRelabel.lean#L126-L134

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_hilbFn_map_rename_19bfaf389bfb (I : Ideal (MRing ι₁ F)) (m : K₂ → ℤ) :
    hilbFn (I.map (renameEquiv F φ)) m = hilbFn I (m ∘ e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«Relabel».«hilbFn_map_rename» := P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_hilbFn_map_rename_19bfaf389bfb
