-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagProjTrdegLe_trdeg_blocks_add_one_le_66cd9c388991
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagProjTrdegLe_trdeg_blocks_add_one_le_66cd9c388991
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:07:59.097134+00:00
-- url     : https://prove2.me/theorems/add867ee-d024-50b3-a50b-a2a77137526d
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Proj Trdeg Le trdeg blocks add one le 66cd9c388991: P2 M Ground Theory Heights  Heights Numbers DVR Flag Proj Trdeg Le trdeg blocks add one le 66cd
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Proj Trdeg Le trdeg blocks add one le 66cd9c388991 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Proj Trdeg Le trdeg blocks add one le 66cd9c388991 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagProjTrdegLe.lean#L47-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagProjTrdegLe.lean#L47-L107

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagProjSpecialDimSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosureModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PAdjoinTrdegAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosurePullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagProjTrdegLe
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagProjTrdegLe

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagProjTrdegLe_trdeg_blocks_add_one_le_66cd9c388991 {O Φ : Type} [CommRing O] [Field Φ] [Algebra O Φ]
    (hO : Function.Injective (algebraMap O Φ)) {Λ K' : Type} (ι' : Λ → Type) (j : K' ↪ Λ) (pt : (Σ o, ι' o) → Φ)
    (b : Λ) (hjb : ∀ o, j o ≠ b) (l : ι' b) (hc : pt ⟨b, l⟩ ≠ 0) :
    Algebra.trdeg O (MvPolynomial (Σ o, ι' (j o)) O ⧸ pointIdeal O (fun p => pt (FieldNumbers.blockIncl j ι' p))) + 1 ≤
      Algebra.trdeg O (MvPolynomial (Σ o, ι' o) O ⧸ pointIdeal O pt) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagProjTrdegLe».«trdeg_blocks_add_one_le» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagProjTrdegLe_trdeg_blocks_add_one_le_66cd9c388991
