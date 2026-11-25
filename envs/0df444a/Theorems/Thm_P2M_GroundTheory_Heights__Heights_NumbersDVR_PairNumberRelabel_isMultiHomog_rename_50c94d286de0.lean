-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_isMultiHomog_rename_50c94d286de0
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_isMultiHomog_rename_50c94d286de0
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:22:48.702095+00:00
-- url     : https://prove2.me/theorems/78fa0828-0b66-49c3-a932-6c863010616c
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel is Multi Homog rename 50c94d286de0: P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel is Multi Homog rename 50c94d
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel is Multi Homog rename 50c94d286de0 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel is Multi Homog rename 50c94d286de0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean#L190-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean#L190-L199

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_IntNumRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomog_rename_fd9a6cb3fd55

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_isMultiHomog_rename_50c94d286de0 (hσ : ∀ v, (σ v).1 = e v.1) {f : MRing ι₁ O} {a : K₁ → ℕ}
    (h : IsMultiHomog f a) : IsMultiHomog (rename σ f) (a ∘ e.symm) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«PairNumberRelabel».«isMultiHomog_rename» := P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_isMultiHomog_rename_50c94d286de0
