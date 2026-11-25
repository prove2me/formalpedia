-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_component_form_mul_76a1836436b5
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_component_form_mul_76a1836436b5
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:13:12.579592+00:00
-- url     : https://prove2.me/theorems/1d99a732-2b8b-563f-8006-5a993d9862e6
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Noetherian component form mul 76a1836436b5: P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Noetherian component form mul 76a1
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Noetherian component form mul 76a1836436b5 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Noetherian component form mul 76a1836436b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHomLocRingNoetherian.lean#L17-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHomLocRingNoetherian.lean#L17-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingNoetherian
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
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingNoetherian
variable {R : Type u} [CommRing R] {K : Type} [DecidableEq K] {ι : K → Type}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_component_form_mul_76a1836436b5 {s : MRing ι R} {e : K → ℕ} (hs : IsMultiHomog s e) (d : K → ℕ)
    (h : MRing ι R) :
    weightedHomogeneousComponent (blockWeight ι) (e + d) (s * h) =
      s * weightedHomogeneousComponent (blockWeight ι) d h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«HomLocRingNoetherian».«component_form_mul» := P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_component_form_mul_76a1836436b5
