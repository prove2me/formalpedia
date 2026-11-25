-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_ren_apply_85b054347a53
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_ren_apply_85b054347a53
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:13:54.134921+00:00
-- url     : https://prove2.me/theorems/fea67cb6-63b0-4968-af98-4c51e0baa796
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel ren apply 85b054347a53: P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel ren apply 85b054347a53
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel ren apply 85b054347a53 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel ren apply 85b054347a53 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean#L24-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean#L24-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_IntNumRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_ren_apply_8f65176f1b12

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_ren_apply_85b054347a53 (f : MRing ι₁ R) : ren (R := R) σ f = rename σ f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«PairNumberRelabel».«ren_apply» := P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_ren_apply_85b054347a53
