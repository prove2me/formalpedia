-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_isRelevant_iff__96fb149ae8ef
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_isRelevant_iff__96fb149ae8ef
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:55:56.492559+00:00
-- url     : https://prove2.me/theorems/bca51672-8999-5c0f-9649-d159f1a41d2f
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel is Relevant iff  96fb149ae8ef: P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel is Relevant iff  96fb149ae8ef
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel is Relevant iff  96fb149ae8ef construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel is Relevant iff  96fb149ae8ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean#L47-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean#L47-L53

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
variable {K₁ K₂ : Type} {ι₁ : K₁ → Type} {ι₂ : K₂ → Type} {R : Type} [CommRing R]
  (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k))

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_isRelevant_iff__96fb149ae8ef {K : Type} {ι : K → Type} (W : Ideal (MRing ι R)) :
    IsRelevant W ↔ ∀ k, ∃ p : Σ k, ι k, p.1 = k ∧ (X p : MRing ι R) ∉ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«PairNumberRelabel».«isRelevant_iff'» := P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_isRelevant_iff__96fb149ae8ef
