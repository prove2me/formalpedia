-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_specialIdeal_map_26c26a49f2d7
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_specialIdeal_map_26c26a49f2d7
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:58:21.712425+00:00
-- url     : https://prove2.me/theorems/278d5128-438e-41f6-9f7d-29095bd29904
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel special Ideal map 26c26a49f2d7: P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel special Ideal map 26c26a49f2d7
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel special Ideal map 26c26a49f2d7 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel special Ideal map 26c26a49f2d7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean#L150-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean#L150-L158

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
omit [DecidableEq K₁] [DecidableEq K₂]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_specialIdeal_map_26c26a49f2d7 (W : Ideal (MRing ι₁ O)) :
    specialIdeal (W.map (ren (R := O) σ : MRing ι₁ O →+* MRing ι₂ O)) =
      (specialIdeal W).map (renameEquiv (IsLocalRing.ResidueField O) σ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«PairNumberRelabel».«specialIdeal_map» := P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_specialIdeal_map_26c26a49f2d7
