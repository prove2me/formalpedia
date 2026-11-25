-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_contDiff_factor_240d0b9df1f0
-- name    : P2M_GroundTheory_Heights__Heights_FourB_contDiff_factor_240d0b9df1f0
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:46:42.737967+00:00
-- url     : https://prove2.me/theorems/122020d1-adcb-4352-937e-98c097584559
-- title:
--   P2 M Ground Theory Heights  Heights Four B cont Diff factor 240d0b9df1f0: P2 M Ground Theory Heights  Heights Four B cont Diff factor 240d0b9df1f0
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B cont Diff factor 240d0b9df1f0 construction uses the P2 M Ground Theory Heights  Heights Four B cont Diff factor 240d0b9df1f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PFlagWeightLevi.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PFlagWeightLevi.lean#L23-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsDeriv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PFlagWeightLevi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_FourB_contDiff_factor_240d0b9df1f0 {f N : ℕ} (τ : Fin f) :
    ContDiff ℝ 2 fun z : (Σ _ : Fin f, LowerPair N) → ℂ => fun q : LowerPair N => z ⟨τ, q⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«contDiff_factor» := P2M_GroundTheory_Heights__Heights_FourB_contDiff_factor_240d0b9df1f0
