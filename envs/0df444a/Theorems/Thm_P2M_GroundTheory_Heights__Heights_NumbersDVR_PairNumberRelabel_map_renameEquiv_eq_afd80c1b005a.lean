-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_map_renameEquiv_eq_afd80c1b005a
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_map_renameEquiv_eq_afd80c1b005a
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:04:28.834796+00:00
-- url     : https://prove2.me/theorems/e18d3de5-ebea-410e-b5cb-19865d06fabf
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel map rename Equiv eq afd80c1b005a: P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel map rename Equiv eq afd80c1b00
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel map rename Equiv eq afd80c1b005a construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel map rename Equiv eq afd80c1b005a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean#L29-L30

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_map_renameEquiv_eq_afd80c1b005a (I : Ideal (MRing ι₁ R)) :
    I.map (renameEquiv R σ) = I.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«PairNumberRelabel».«map_renameEquiv_eq» := P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_map_renameEquiv_eq_afd80c1b005a
