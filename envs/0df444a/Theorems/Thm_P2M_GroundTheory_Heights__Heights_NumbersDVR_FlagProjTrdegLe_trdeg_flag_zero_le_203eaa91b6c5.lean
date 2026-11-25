-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagProjTrdegLe_trdeg_flag_zero_le_203eaa91b6c5
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagProjTrdegLe_trdeg_flag_zero_le_203eaa91b6c5
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:08:21.301944+00:00
-- url     : https://prove2.me/theorems/27d0e890-b8cf-47db-81e5-1cacc70bb9ec
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Proj Trdeg Le trdeg flag zero le 203eaa91b6c5: P2 M Ground Theory Heights  Heights Numbers DVR Flag Proj Trdeg Le trdeg flag zero le 203eaa91b6c5
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Proj Trdeg Le trdeg flag zero le 203eaa91b6c5 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Proj Trdeg Le trdeg flag zero le 203eaa91b6c5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagProjTrdegLe.lean#L115-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagProjTrdegLe.lean#L115-L135

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagProjTrdegLe_trdeg_flag_zero_le_203eaa91b6c5 {O Ω K : Type} [CommRing O] [Field Ω] [Algebra O Ω] {ι : K → Type} {N M M' : ℕ}
    {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
    (y : (Σ k, ι k) → Ω) (w e : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E)
    (φ' : Fin M' → Module.Dual Ω E) (t : Fin N → Φ) :
    Algebra.trdeg O (MRing (bundleIdx (bundleIdx ι M) M') O ⧸ pointIdeal O (flagClosurePt y w e φ φ' t 0)) ≤
      Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagProjTrdegLe».«trdeg_flag_zero_le» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagProjTrdegLe_trdeg_flag_zero_le_203eaa91b6c5
