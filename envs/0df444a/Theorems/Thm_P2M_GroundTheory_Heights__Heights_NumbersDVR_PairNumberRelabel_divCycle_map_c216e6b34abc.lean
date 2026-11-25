-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_divCycle_map_c216e6b34abc
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_divCycle_map_c216e6b34abc
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:16:51.389841+00:00
-- url     : https://prove2.me/theorems/be23897b-980b-5105-a0d5-35c91962120c
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel div Cycle map c216e6b34abc: P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel div Cycle map c216e6b34abc
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel div Cycle map c216e6b34abc construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel div Cycle map c216e6b34abc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean#L73-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean#L73-L96

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
variable (e : K₁ ≃ K₂)

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_divCycle_map_c216e6b34abc (hσ : ∀ v, (σ v).1 = e v.1) (P W : Ideal (MRing ι₁ R)) (f : MRing ι₁ R) :
    divCycle (P.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R)) (rename σ f)
        (W.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R)) = divCycle P f W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«PairNumberRelabel».«divCycle_map» := P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_divCycle_map_c216e6b34abc
